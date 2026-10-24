//! Lock-free registration queues for parked senders/receivers.
//!
//! `WaitList` replaces the `Mutex<LinkedList<Arc<dyn Notifier>>>` that used
//! to back `bounded`/`unbounded`'s `senders`/`receivers` lists with
//! [`kovan_queue::seg_queue::SegQueue`], the workspace's own lock-free MPMC
//! queue. `register` pushes; `notify_one`/`notify_all` pop and notify.
//!
//! # The loss-free wakeup contract
//!
//! A channel operation that finds its condition unmet (full, on send; empty,
//! on recv) always follows the same two-phase shape:
//!
//! 1. **Register**: unconditionally push a fresh [`Notifier`] onto the
//!    relevant `WaitList`.
//! 2. **Fence**: [`wakeup_fence`] -- a `SeqCst` fence.
//! 3. **Recheck**: re-read the condition. If it is now satisfiable, resolve
//!    immediately and *abandon* the just-pushed entry ([`WaitList::abandon`],
//!    see below). Otherwise, actually wait (park / return `Pending`).
//!
//! The producing side (the operation that changes the condition -- a
//! message enqueue, a freed slot, a disconnect) mirrors this:
//!
//! 1. **Publish**: make the state change visible (enqueue the message /
//!    decrement `len` / store the disconnect flag).
//! 2. **Fence**: [`wakeup_fence`].
//! 3. **Scan**: `notify_one`/`notify_all` on the relevant `WaitList`.
//!
//! ## Why the fence, not just Acquire/Release on `len`/the message queue
//!
//! The two checks above touch *two independent memory locations*: the
//! registration queue and the condition (`len`, the message queue's
//! head/tail, the disconnect flag). Acquire/Release on each variable
//! separately is not enough to rule out both sides missing each other --
//! that is the textbook store-buffering anomaly: thread A writes x then
//! reads y; thread B writes y then reads x; with only acquire/release,
//! both reads can observe the pre-write value. Sandwiching *both* sides
//! with a `SeqCst` fence closes that gap: `fence(SeqCst)` participates in a
//! single total order shared by every `SeqCst` fence, and per the C++/Rust
//! memory model, an atomic operation sequenced after such a fence is
//! ordered after it in that total order, and one sequenced before it is
//! ordered before it. Consequently, if the receiver's post-fence recheck
//! (step 3 above) fails to observe the sender's publish (step 1 on the
//! sender), the sender's post-fence scan (its step 3) is guaranteed to
//! observe the receiver's registration (its step 1) -- the receiver's
//! `Notifier` is in the queue by the time the sender scans it, regardless
//! of `SegQueue`'s own internal ordering choices, because the fence forces
//! *some* memory operation on each side (the queue's own internal atomics)
//! into the shared total order.
//!
//! ## Why registration can go stale, and why that's still loss-free
//!
//! Because registration is unconditional (step 1 happens before the
//! recheck can decide it wasn't needed), a registering thread can end up
//! abandoning its own entry -- it never parks/never returns `Pending`,
//! because the recheck in step 3 already found the condition satisfied (or
//! an async operation completes, or is dropped, while its entry is queued).
//! Left alone, that entry would sit in the queue looking exactly like a
//! live waiter, and a later `notify_one` could pop *it* instead of an
//! actually-parked waiter, wasting the one wakeup that message was
//! supposed to deliver.
//!
//! A signal has three states, waiting, notified and cancelled, and a waiter
//! leaves the first for exactly one of the others, by compare-and-swap:
//! `notify_one` delivers with [`Notifier::try_notify`], which only a waiting
//! entry accepts (it pops on past any other), and the abandoning thread
//! withdraws its entry with [`Notifier::cancel`]. When the cancel loses, a
//! notifier delivered a wakeup to the entry between the recheck and the
//! cancel, one the abandoning thread is not going to use, so it passes it on
//! with a `notify_one` of its own. A wakeup is therefore spent on a waiter
//! that waits, or handed on; never on an entry nobody waits on. (Marking the
//! entry stale with `notify()` after the take, as this crate did before,
//! left that window open: the TLA+ model, `proofs/tla/channel`, found it.)

use crate::signal::{AsyncSignal, Notifier};
use kovan_queue::seg_queue::SegQueue;
use std::sync::Arc;
use std::sync::atomic::Ordering;
use std::task::Waker;

// Shuttle's own `fence` is (as of shuttle 0.9) a documented no-op under the
// checker -- shuttle already treats every atomic operation as `SeqCst`, so
// this call adds no scheduling point either way, unlike the `AtomicUsize`/
// `AtomicBool` swaps in `signal.rs`/`flavors::unbounded`/`flavors::bounded`,
// which are what actually make the register/publish race explorable.
// Swapped anyway so this module consistently reaches for shuttle's atomic
// API under the feature, matching every other call site.
#[cfg(feature = "shuttle")]
use shuttle::sync::atomic::fence;
#[cfg(not(feature = "shuttle"))]
use std::sync::atomic::fence;

/// The `SeqCst` fence pairing registration with recheck, and publish with
/// notify. Named (rather than inlined at each call site) so every use sites
/// visibly agrees on the same ordering choice -- see the module docs above
/// for the full justification.
#[inline]
pub(crate) fn wakeup_fence() {
    fence(Ordering::SeqCst);
}

/// A lock-free FIFO of parked waiters (threads or async tasks) awaiting
/// notification on one side of a channel.
pub(crate) struct WaitList {
    queue: SegQueue<Arc<dyn Notifier>>,
}

impl Default for WaitList {
    fn default() -> Self {
        Self::new()
    }
}

impl WaitList {
    pub(crate) fn new() -> Self {
        Self {
            queue: SegQueue::new(),
        }
    }

    /// Registers a waiter. Must be paired with [`wakeup_fence`] and a
    /// recheck of the condition being waited on -- see the module docs.
    pub(crate) fn register(&self, notifier: Arc<dyn Notifier>) {
        self.queue.push(notifier);
    }

    /// Wakes exactly one live waiter, popping past stale entries so a real
    /// wakeup is never wasted on one. No-op if the queue is empty or every
    /// entry in it is stale.
    pub(crate) fn notify_one(&self) {
        while let Some(notifier) = self.queue.pop() {
            if notifier.try_notify() {
                return;
            }
        }
    }

    /// Withdraws an entry its owner registered on this list and no longer
    /// waits on; when a notifier woke it first, passes that wakeup on to the
    /// next waiter. See the module docs.
    pub(crate) fn abandon(&self, notifier: &dyn Notifier) {
        if !notifier.cancel() {
            self.notify_one();
        }
    }

    /// Wakes every currently queued waiter, live or stale (used on
    /// disconnect, where every waiter must observe the new state).
    pub(crate) fn notify_all(&self) {
        while let Some(notifier) = self.queue.pop() {
            notifier.notify();
        }
    }
}

/// An async operation's registration on a wait list: the signal it waits on,
/// and whether an entry of it may still be queued. The three async channel
/// operations share it, so they follow one protocol: register at most one
/// entry at a time, take a wakeup a notifier delivered as the poll's own, and
/// abandon the entry when the operation completes or is dropped without
/// using it (see the module docs).
pub(crate) struct AsyncWait {
    signal: Arc<AsyncSignal>,
    queued: bool,
}

impl AsyncWait {
    pub(crate) fn new() -> Self {
        Self {
            signal: Arc::new(AsyncSignal::new()),
            queued: false,
        }
    }

    /// At a poll's start: a notifier that woke the signal popped its entry,
    /// and the wakeup is this poll's.
    pub(crate) fn begin_poll(&mut self) {
        if self.queued && self.signal.was_woken() {
            self.queued = false;
        }
    }

    /// Registers for a wakeup on `list`: the waker updated, and an entry
    /// queued unless one already is. The caller fences and re-checks after.
    pub(crate) fn register(&mut self, list: &WaitList, waker: &Waker) {
        if self.queued {
            self.signal.register(waker);
            return;
        }
        if self.signal.is_notified() {
            self.signal = Arc::new(AsyncSignal::new());
        }
        self.signal.register(waker);
        list.register(self.signal.clone());
        self.queued = true;
    }

    /// The operation completes, or is dropped, while an entry may be queued
    /// on `list`: withdraw it, or pass on a wakeup it took and did not use.
    pub(crate) fn finish(&mut self, list: &WaitList) {
        if self.queued {
            self.queued = false;
            list.abandon(&*self.signal);
        }
    }
}
