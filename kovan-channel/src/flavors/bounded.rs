#[cfg(not(target_arch = "wasm32"))]
use crate::flavors::RecvDeadline;
use crate::flavors::unbounded;
use crate::signal::Notifier;
#[cfg(not(target_arch = "wasm32"))]
use crate::signal::Signal;
use crate::waitlist::{AsyncWait, WaitList, wakeup_fence};
#[cfg(not(target_arch = "wasm32"))]
use crossbeam_utils::Backoff;
use std::sync::Arc;
use std::sync::atomic::Ordering;
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;

// Shuttle-instrumented so `len`/`sender_count`/`disconnected` -- raced by
// a blocking `send`/`recv`'s register/recheck against the other side's
// publish/notify, see `crate::waitlist` -- are checker scheduling points,
// matching `signal.rs`'s `Signal` swap.
#[cfg(feature = "shuttle")]
use shuttle::sync::atomic::{AtomicBool, AtomicUsize};
#[cfg(not(feature = "shuttle"))]
use std::sync::atomic::{AtomicBool, AtomicUsize};

struct Channel<T: 'static> {
    sender: unbounded::Sender<T>,
    receiver: unbounded::Receiver<T>,
    capacity: usize,
    len: AtomicUsize,
    senders: WaitList,
    receivers: WaitList,
    /// Number of live bounded Sender handles.
    sender_count: AtomicUsize,
    /// Set when all bounded senders are dropped.
    disconnected: AtomicBool,
    /// Number of live Receiver handles.
    receiver_count: AtomicUsize,
    /// Set when every Receiver is dropped: no value sent can be taken, so a
    /// send no longer waits for room.
    receivers_gone: AtomicBool,
}

/// The sending half of a bounded channel.
pub struct Sender<T: 'static> {
    inner: Arc<Channel<T>>,
}

impl<T: 'static> Clone for Sender<T> {
    fn clone(&self) -> Self {
        self.inner.sender_count.fetch_add(1, Ordering::Relaxed);
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T: 'static> Drop for Sender<T> {
    fn drop(&mut self) {
        if self.inner.sender_count.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.inner.disconnected.store(true, Ordering::Release);
            // Loss-free wakeup: pairs with every receiver's
            // register-then-recheck. See `crate::waitlist` module docs.
            wakeup_fence();
            self.inner.receivers.notify_all();
        }
    }
}

unsafe impl<T: 'static + Send> Send for Sender<T> {}
unsafe impl<T: 'static + Send> Sync for Sender<T> {}

/// The receiving half of a bounded channel.
pub struct Receiver<T: 'static> {
    inner: Arc<Channel<T>>,
}

impl<T: 'static> Clone for Receiver<T> {
    fn clone(&self) -> Self {
        self.inner.receiver_count.fetch_add(1, Ordering::Relaxed);
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T: 'static> Drop for Receiver<T> {
    fn drop(&mut self) {
        if self.inner.receiver_count.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.inner.receivers_gone.store(true, Ordering::Release);
            // Loss-free wakeup: pairs with every sender's register-then-
            // recheck. See `crate::waitlist` module docs.
            wakeup_fence();
            self.inner.senders.notify_all();
        }
    }
}

unsafe impl<T: 'static + Send> Send for Receiver<T> {}
unsafe impl<T: 'static + Send> Sync for Receiver<T> {}

impl<T: 'static> Channel<T> {
    fn new(capacity: usize) -> Self {
        let (sender, receiver) = unbounded::channel();
        Self {
            sender,
            receiver,
            capacity,
            len: AtomicUsize::new(0),
            senders: WaitList::new(),
            receivers: WaitList::new(),
            sender_count: AtomicUsize::new(1),
            disconnected: AtomicBool::new(false),
            receiver_count: AtomicUsize::new(1),
            receivers_gone: AtomicBool::new(false),
        }
    }
}

impl<T: 'static> Sender<T> {
    /// Sends a message into the channel, blocking if full.
    ///
    /// Once every receiver is gone the value is dropped and `send` returns at
    /// once: no receiver can ever take it ([`is_disconnected`](Self::is_disconnected)).
    #[cfg(not(target_arch = "wasm32"))]
    pub fn send(&self, t: T) {
        let backoff = Backoff::new();
        loop {
            if self.is_disconnected() {
                return;
            }
            let len = self.inner.len.load(Ordering::Relaxed);
            if len >= self.inner.capacity {
                // Register unconditionally, then recheck -- the loss-free
                // wakeup protocol documented in `crate::waitlist`.
                let signal = Arc::new(Signal::new());
                self.inner.senders.register(signal.clone());
                wakeup_fence();

                if self.inner.len.load(Ordering::Acquire) < self.inner.capacity
                    || self.is_disconnected()
                {
                    // Capacity freed up (or every receiver went) between our
                    // first check and registering: we won't actually wait,
                    // so abandon our own entry (see `waitlist` docs) and retry.
                    self.inner.senders.abandon(&*signal);
                    continue;
                }

                signal.wait();
                continue;
            }

            // Try to reserve a slot
            if self
                .inner
                .len
                .compare_exchange(len, len + 1, Ordering::Acquire, Ordering::Relaxed)
                .is_ok()
            {
                // Success, send the message
                self.inner.sender.send(t);

                // Notify one receiver
                wakeup_fence();
                self.inner.receivers.notify_one();

                return;
            }
            // Failed to reserve, retry
            backoff.snooze();
        }
    }
    /// Returns `true` if every receiver has been dropped: a send then drops
    /// its value and returns at once.
    pub fn is_disconnected(&self) -> bool {
        self.inner.receivers_gone.load(Ordering::Acquire)
    }

    /// Returns true if the channel is full.
    pub fn is_full(&self) -> bool {
        self.inner.len.load(Ordering::Relaxed) >= self.inner.capacity
    }

    /// Registers a signal for notification when space becomes available.
    ///
    /// This is the primitive `select!` builds on to wait across multiple
    /// channels with a single `Signal`. It exposes step 1 of the crate's
    /// register -> fence -> recheck -> park loss-free wakeup protocol (see
    /// the `crate::waitlist` module docs) without the other three steps:
    /// the caller owns the rest of the contract -- after registering on
    /// every channel it cares about, it MUST call
    /// `crate::waitlist::wakeup_fence` (or an equivalent `SeqCst` fence)
    /// and then recheck every channel's condition *before*
    /// parking/awaiting on `signal`. Skipping the fence or the recheck
    /// reopens the exact store-buffering race the protocol exists to
    /// close, and a real wakeup can be silently lost.
    ///
    /// A signal another channel already notified may be registered (the
    /// one `Signal` of a `select!` is registered on its channels one after
    /// another): its entry is stale and skipped, and the caller's wait
    /// returns at once. A caller that stops waiting without being woken must
    /// withdraw the signal ([`Signal::cancel`](crate::signal::Signal::cancel))
    /// and, when that answers `false`, pass the wakeup it took on with
    /// [`wake_one_waiter`](Self::wake_one_waiter) on every channel it
    /// registered on.
    pub fn register_signal(&self, signal: Arc<dyn Notifier>) {
        self.inner.senders.register(signal);
    }

    /// Wakes one sender waiting on this channel, if any: how a caller of
    /// [`register_signal`](Self::register_signal) passes on a wakeup its
    /// signal took and did not use.
    pub fn wake_one_waiter(&self) {
        self.inner.senders.notify_one();
    }

    /// Sends a message into the channel asynchronously.
    pub async fn send_async(&self, t: T) {
        use std::future::Future;
        use std::pin::Pin;
        use std::task::{Context, Poll};

        struct SendFuture<'a, T: 'static> {
            sender: &'a Sender<T>,
            t: Option<T>,
            wait: AsyncWait,
        }

        impl<'a, T: 'static> Unpin for SendFuture<'a, T> {}

        impl<'a, T: 'static> SendFuture<'a, T> {
            /// Reserves a slot and sends, when there is room.
            fn try_send(&mut self) -> bool {
                let inner = &self.sender.inner;
                let len = inner.len.load(Ordering::Acquire);
                if len < inner.capacity
                    && inner
                        .len
                        .compare_exchange(len, len + 1, Ordering::Acquire, Ordering::Relaxed)
                        .is_ok()
                {
                    if let Some(t) = self.t.take() {
                        inner.sender.send(t);
                    }
                    // Notify one receiver
                    wakeup_fence();
                    inner.receivers.notify_one();
                    true
                } else {
                    false
                }
            }
        }

        impl<'a, T: 'static> Future for SendFuture<'a, T> {
            type Output = ();

            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let this = self.get_mut();
                this.wait.begin_poll();
                // Every receiver gone: the value is dropped, as `send` does.
                if this.sender.is_disconnected() || this.try_send() {
                    this.t = None;
                    this.wait.finish(&this.sender.inner.senders);
                    return Poll::Ready(());
                }

                this.wait.register(&this.sender.inner.senders, cx.waker());
                wakeup_fence();

                // Re-check: capacity may have freed up, or every receiver
                // gone, since the fast-path attempt above.
                if this.sender.is_disconnected() || this.try_send() {
                    this.t = None;
                    this.wait.finish(&this.sender.inner.senders);
                    return Poll::Ready(());
                }

                Poll::Pending
            }
        }

        // Dropped while pending: its entry must not take a wakeup meant for
        // a sender that waits.
        impl<'a, T: 'static> Drop for SendFuture<'a, T> {
            fn drop(&mut self) {
                self.wait.finish(&self.sender.inner.senders);
            }
        }

        SendFuture {
            sender: self,
            t: Some(t),
            wait: AsyncWait::new(),
        }
        .await
    }
}

impl<T: 'static> Receiver<T> {
    /// Returns true if the channel is empty.
    pub fn is_empty(&self) -> bool {
        // This is approximate
        self.inner.receiver.is_empty()
    }

    /// Registers a signal for notification when a message arrives.
    ///
    /// This is the primitive `select!` builds on to wait across multiple
    /// channels with a single `Signal`. It exposes step 1 of the crate's
    /// register -> fence -> recheck -> park loss-free wakeup protocol (see
    /// the `crate::waitlist` module docs) without the other three steps:
    /// the caller owns the rest of the contract -- after registering on
    /// every channel it cares about, it MUST call
    /// `crate::waitlist::wakeup_fence` (or an equivalent `SeqCst` fence)
    /// and then recheck every channel's condition *before*
    /// parking/awaiting on `signal`. Skipping the fence or the recheck
    /// reopens the exact store-buffering race the protocol exists to
    /// close, and a real wakeup can be silently lost.
    ///
    /// A signal another channel already notified may be registered (the
    /// one `Signal` of a `select!` is registered on its channels one after
    /// another): its entry is stale and skipped, and the caller's wait
    /// returns at once. A caller that stops waiting without being woken must
    /// withdraw the signal ([`Signal::cancel`](crate::signal::Signal::cancel))
    /// and, when that answers `false`, pass the wakeup it took on with
    /// [`wake_one_waiter`](Self::wake_one_waiter) on every channel it
    /// registered on.
    pub fn register_signal(&self, signal: Arc<dyn Notifier>) {
        self.inner.receivers.register(signal);
    }

    /// Wakes one receiver waiting on this channel, if any: how a caller of
    /// [`register_signal`](Self::register_signal) passes on a wakeup its
    /// signal took and did not use.
    pub fn wake_one_waiter(&self) {
        self.inner.receivers.notify_one();
    }
    /// Attempts to receive a message from the channel without blocking.
    pub fn try_recv(&self) -> Option<T> {
        // Try to receive from the underlying queue
        // Note: unbounded::Receiver::try_recv returns None if empty
        match self.inner.receiver.try_recv() {
            Some(msg) => {
                // Decrement length
                self.inner.len.fetch_sub(1, Ordering::Release);

                // Notify one sender
                wakeup_fence();
                self.inner.senders.notify_one();

                Some(msg)
            }
            None => None,
        }
    }

    /// Returns `true` if all senders have been dropped.
    pub fn is_disconnected(&self) -> bool {
        self.inner.disconnected.load(Ordering::Acquire)
    }

    /// Receives a message from the channel, blocking if empty.
    ///
    /// Returns `None` when the channel is empty **and** all senders have been dropped.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn recv(&self) -> Option<T> {
        if let Some(msg) = self.try_recv() {
            return Some(msg);
        }

        if self.is_disconnected() {
            return self.try_recv();
        }

        loop {
            // Register unconditionally, then recheck -- the loss-free
            // wakeup protocol documented in `crate::waitlist`.
            let signal = Arc::new(Signal::new());
            self.inner.receivers.register(signal.clone());
            wakeup_fence();

            if let Some(msg) = self.try_recv() {
                // We registered but found a message already: not going to
                // wait, so abandon our own entry (see `waitlist` docs).
                self.inner.receivers.abandon(&*signal);
                return Some(msg);
            }

            if self.is_disconnected() {
                self.inner.receivers.abandon(&*signal);
                return self.try_recv();
            }

            signal.wait();

            if let Some(msg) = self.try_recv() {
                return Some(msg);
            }

            // Drain once more rather than trusting the try_recv
            // immediately above: that try_recv and this is_disconnected
            // read are independent atomics with no ordering link forcing
            // them to agree, so observing disconnected here does not by
            // itself prove that same-thread, immediately-prior try_recv
            // already saw every message a sender published before
            // disconnecting -- see `unbounded::Receiver::recv`'s final
            // check for the full argument (found by shuttle once the
            // blocking path's own atomics became checker scheduling
            // points).
            if self.is_disconnected() {
                return self.try_recv();
            }
        }
    }

    /// Receives a message from the channel, blocking until either a
    /// message arrives or `deadline` passes.
    ///
    /// Mirrors [`recv`](Self::recv)'s register -> fence -> recheck -> park
    /// loop (see `crate::waitlist` for the loss-free wakeup contract),
    /// swapping the unbounded park for [`Signal::wait_deadline`] so a
    /// caller never blocks past its budget. `Timeout` and `Disconnected`
    /// are kept distinct (see [`RecvDeadline`]) because a caller bounding
    /// an internal wait wants to treat them differently: a timeout is
    /// worth retrying or escalating, a disconnect never will be.
    #[cfg(not(target_arch = "wasm32"))]
    pub fn recv_deadline(&self, deadline: Instant) -> RecvDeadline<T> {
        if let Some(msg) = self.try_recv() {
            return RecvDeadline::Msg(msg);
        }

        if self.is_disconnected() {
            return match self.try_recv() {
                Some(msg) => RecvDeadline::Msg(msg),
                None => RecvDeadline::Disconnected,
            };
        }

        loop {
            // Register unconditionally, then recheck -- the loss-free
            // wakeup protocol documented in `crate::waitlist`.
            let signal = Arc::new(Signal::new());
            self.inner.receivers.register(signal.clone());
            wakeup_fence();

            if let Some(msg) = self.try_recv() {
                // We registered but found a message already: not going to
                // wait, so abandon our own entry (see `waitlist` docs).
                self.inner.receivers.abandon(&*signal);
                return RecvDeadline::Msg(msg);
            }

            if self.is_disconnected() {
                self.inner.receivers.abandon(&*signal);
                return match self.try_recv() {
                    Some(msg) => RecvDeadline::Msg(msg),
                    None => RecvDeadline::Disconnected,
                };
            }

            if !signal.wait_deadline(deadline) {
                // Timed out: mark our own entry stale (see `waitlist`
                // docs) and do one last recheck -- a message or disconnect
                // may have landed in the instant the deadline passed.
                self.inner.receivers.abandon(&*signal);
                if let Some(msg) = self.try_recv() {
                    return RecvDeadline::Msg(msg);
                }
                if !self.is_disconnected() {
                    return RecvDeadline::Timeout;
                }
                // Disconnected: drain once more rather than trusting the
                // try_recv just above (see `unbounded::Receiver::recv`'s
                // final check for why that try_recv and this
                // is_disconnected read can legitimately disagree).
                return match self.try_recv() {
                    Some(msg) => RecvDeadline::Msg(msg),
                    None => RecvDeadline::Disconnected,
                };
            }

            // Woken -- either a message arrived or senders disconnected.
            if let Some(msg) = self.try_recv() {
                return RecvDeadline::Msg(msg);
            }

            if self.is_disconnected() {
                return match self.try_recv() {
                    Some(msg) => RecvDeadline::Msg(msg),
                    None => RecvDeadline::Disconnected,
                };
            }

            // Spurious wake with nothing to show: loop back and
            // re-register. `wait_deadline` re-derives "has `deadline`
            // passed" from the clock on every call, so this cannot
            // overrun its budget no matter how many spurious iterations
            // happen first.
        }
    }

    /// Receives a message from the channel asynchronously.
    ///
    /// Returns `None` when the channel is empty and all senders have been dropped.
    pub async fn recv_async(&self) -> Option<T> {
        use std::future::Future;
        use std::pin::Pin;
        use std::task::{Context, Poll};

        struct RecvFuture<'a, T: 'static> {
            receiver: &'a Receiver<T>,
            wait: AsyncWait,
        }

        impl<'a, T: 'static> Unpin for RecvFuture<'a, T> {}

        impl<'a, T: 'static> Future for RecvFuture<'a, T> {
            type Output = Option<T>;

            fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
                let this = self.get_mut();
                let list = &this.receiver.inner.receivers;
                this.wait.begin_poll();
                if let Some(msg) = this.receiver.try_recv() {
                    this.wait.finish(list);
                    return Poll::Ready(Some(msg));
                }

                // Disconnected and empty: done (drain any remaining buffered messages).
                if this.receiver.is_disconnected() {
                    this.wait.finish(list);
                    return Poll::Ready(this.receiver.try_recv());
                }

                this.wait.register(list, cx.waker());
                wakeup_fence();

                // Re-check: a send or disconnect may have landed between the first
                // check and signal registration.
                if let Some(msg) = this.receiver.try_recv() {
                    this.wait.finish(list);
                    return Poll::Ready(Some(msg));
                }

                if this.receiver.is_disconnected() {
                    this.wait.finish(list);
                    // Drain once more rather than trusting the try_recv
                    // just above (see `unbounded::Receiver::recv`'s final
                    // check for why that try_recv and this
                    // is_disconnected read can legitimately disagree).
                    return Poll::Ready(this.receiver.try_recv());
                }

                Poll::Pending
            }
        }

        // Dropped while pending: its entry must not take a wakeup meant for
        // a receiver that waits.
        impl<'a, T: 'static> Drop for RecvFuture<'a, T> {
            fn drop(&mut self) {
                self.wait.finish(&self.receiver.inner.receivers);
            }
        }

        RecvFuture {
            receiver: self,
            wait: AsyncWait::new(),
        }
        .await
    }
}

/// Creates a channel of bounded capacity.
pub fn channel<T: 'static>(cap: usize) -> (Sender<T>, Receiver<T>) {
    assert!(
        cap > 0,
        "bounded channel capacity must be greater than zero"
    );
    let inner = Arc::new(Channel::new(cap));
    (
        Sender {
            inner: inner.clone(),
        },
        Receiver { inner },
    )
}
