//! Progress: each operation kovan runs completes in a bounded number of
//! its own steps while other threads are held at chosen points of theirs
//! (see `stall`): inside a traversal, mid insert, in a slow path, mid
//! hand-over, mid exit, mid flush. Where a loop's pass count is the bound,
//! a hook at that loop's step counts it.

use super::{
    Counted, Hold, eventually, join_within, lock, own_tid, published_epoch, spend_first_retire,
    with_handle,
};
use crate::guard::{flush, pin, retire};
use crate::reclaim::MAX_CACHE;
use crate::retired::RetiredNode;
use crate::slot::{EPOCH_UNCONDITIONAL, RETIRE_FREQ};
use crate::stall::{self, Step};
use std::boxed::Box;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::thread;

/// A thread stalled for good in its slow path: an active slot publishing
/// `epoch`, its help request open. `finish` resumes it as the end of its
/// slow path would (both seqnos past the transition, no request open) and
/// then leaves as an exit does, on the calling thread (which needs an ID).
struct FakePending {
    tid: usize,
    seqno: u64,
}

impl FakePending {
    fn open(epoch: u64) -> Self {
        let global = crate::slot::global();
        let tid = global.alloc_tid();
        let slots = global.thread_slots(tid);
        let seqno = slots.epoch[0].load_hi();
        slots.first[0].store_hi(seqno, Ordering::SeqCst);
        slots.epoch[0].store_lo(epoch, Ordering::SeqCst);
        slots.first[0].store_lo(0, Ordering::SeqCst);
        slots.state[0].pointer.store(0, Ordering::SeqCst);
        slots.state[0].parent.store(0, Ordering::SeqCst);
        slots.state[0].epoch.store(0, Ordering::SeqCst);
        slots.state[0]
            .result
            .store(crate::retired::INVPTR as u64, seqno, Ordering::SeqCst);
        global.inc_slow();
        Self { tid, seqno }
    }

    fn finish(self) {
        let global = crate::slot::global();
        let slots = global.thread_slots(self.tid);
        slots.state[0].result.store(0, 0, Ordering::SeqCst);
        slots.epoch[0].store_hi(self.seqno + 2, Ordering::SeqCst);
        slots.first[0].store_hi(self.seqno + 2, Ordering::SeqCst);
        global.dec_slow();
        for first in global.deactivate_slots(self.tid) {
            if first != 0 {
                with_handle(|h| unsafe { h.traverse_into_cache(first as *mut RetiredNode) });
            }
        }
        global.release_tid(self.tid);
    }
}

/// Whether the head of `tid`'s slot list is an entry whose insert has not
/// yet linked the list it displaced (a retire held mid insert there).
fn head_is_unlinked(tid: usize) -> bool {
    let head = crate::slot::global().thread_slots(tid).first[0].load_lo() as *mut RetiredNode;
    !head.is_null()
        && head as usize != crate::retired::INVPTR
        && unsafe { (*head).next.load(Ordering::Acquire) }.is_null()
}

/// On a fresh thread with an ID: flush until every counted value is
/// freed, failing the test if they are not by `DEADLINE`.
pub(super) fn drain(live: &Arc<AtomicUsize>) {
    let l = Arc::clone(live);
    join_within(
        thread::spawn(move || {
            own_tid();
            let freed = eventually(|| {
                flush();
                l.load(Ordering::SeqCst) == 0
            });
            assert!(freed, "{} values never freed", l.load(Ordering::SeqCst));
        }),
        "the drain",
    );
}

/// Parking orphans, adopting them and handing thread IDs over wait for no
/// other thread: with one thread held between the two steps of parking
/// (its ID's orphan word swapped to null, the joined chain not yet stored)
/// and another held after adopting a chain and before merging it, threads
/// keep starting (a first pin claims an ID), retiring, flushing (adopting)
/// and exiting (adopting a chain an earlier exit parked, parking what they
/// cannot place, releasing their ID). The held thread's ID goes to
/// no one before it is released, and once both are let go every retired
/// value is freed exactly once.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn orphans_and_ids_change_hands_while_threads_stall() {
    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));

    // Pinned throughout: its slot is eligible for every batch holding an
    // oldest-born value, so an exiting thread's one-node batch of one
    // cannot be placed and is parked.
    let (pinned_up, pinned_done) = (Hold::new(), Hold::new());
    let pinned = {
        let (up, done) = (pinned_up.clone(), pinned_done.clone());
        thread::spawn(move || {
            let guard = pin();
            up.arrived.store(true, Ordering::SeqCst);
            assert!(eventually(|| done.go.load(Ordering::SeqCst)));
            drop(guard);
            flush();
        })
    };
    pinned_up.reached("the pinned thread");

    // Held at exit, between the two steps of parking its batch.
    let parking = Hold::new();
    let held_tid = Arc::new(AtomicUsize::new(usize::MAX));
    let exiting = {
        let (live, parking, held_tid) = (Arc::clone(&live), parking.clone(), Arc::clone(&held_tid));
        thread::spawn(move || {
            let tid = own_tid();
            held_tid.store(tid, Ordering::SeqCst);
            Counted::retire_oldest(&live);
            parking.arm(Step::OrphanPark, tid);
        })
    };
    parking.reached("the exiting thread");
    let held_tid = held_tid.load(Ordering::SeqCst);

    // Threads that start (a first pin claims an ID), retire and exit while
    // it is held, parking their batch, or flush before they exit, adopting
    // a parked chain.
    let churn = |n: usize, flushing: bool| {
        for _ in 0..n {
            let live = Arc::clone(&live);
            let tid = join_within(
                thread::spawn(move || {
                    let tid = own_tid();
                    Counted::retire_oldest(&live);
                    if flushing {
                        flush();
                    }
                    tid
                }),
                "a thread starting, retiring, flushing and exiting",
            );
            assert_ne!(tid, held_tid, "an exiting thread's ID was taken over");
        }
    };
    churn(8, false);
    // An exit adopts the chain the exit before it parked and, with one
    // eligible slot, places the two batches: whether a chain is parked after
    // the churn depends on how many exits there were. One more exit parks one
    // when none is.
    for _ in 0..2 {
        if crate::slot::orphans_parked() {
            break;
        }
        churn(1, false);
    }
    assert!(
        crate::slot::orphans_parked(),
        "no exit parked a chain for the adopter"
    );

    // Held after taking a chain the churn parked, before merging it.
    let adopting = Hold::new();
    let adopter = {
        let adopting = adopting.clone();
        thread::spawn(move || {
            let tid = own_tid();
            adopting.arm(Step::OrphanAdopt, tid);
            flush();
        })
    };
    adopting.reached("the adopting thread");
    churn(8, false);
    churn(8, true);

    // Still held: the exit has not released its ID (its thread's main
    // function has returned, the exit runs after it), the adopter has not
    // returned from flush().
    assert!(!crate::slot::global().tid_is_released(held_tid));
    assert!(!adopter.is_finished());
    parking.release();
    join_within(exiting, "the held exit");
    adopting.release();
    join_within(adopter, "the held adopter");
    pinned_done.release();
    join_within(pinned, "the pinned thread");

    // Every parked batch is adopted and freed.
    drain(&live);
}

/// A pin's slow path runs no destructor before it republishes its slot. A
/// helper that completed the pending thread's request holds the slot in
/// its hand-over (the epoch seqno odd: new batches skip the slot) and is
/// held there; the pending thread, let go, finishes its slow path without
/// it, and the destructors of what it frees (its free-list cache is full,
/// and its loop traverses a list) run only once its slot is live again.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn slow_path_frees_nothing_before_it_republishes() {
    /// Records whether its thread's slot was closed to new batches (an odd
    /// epoch or list seqno) when it ran: a load it made then would be
    /// unprotected.
    #[repr(C)]
    struct ChecksOpen {
        retired: RetiredNode,
        tid: usize,
        closed: Arc<AtomicUsize>,
        dropped: Arc<AtomicUsize>,
    }
    impl Drop for ChecksOpen {
        fn drop(&mut self) {
            let slots = crate::slot::global().thread_slots(self.tid);
            if (slots.epoch[0].load_hi() | slots.first[0].load_hi()) & 1 != 0 {
                self.closed.fetch_add(1, Ordering::SeqCst);
            }
            self.dropped.fetch_add(1, Ordering::SeqCst);
        }
    }

    let _l = lock();
    let closed = Arc::new(AtomicUsize::new(0));
    let dropped = Arc::new(AtomicUsize::new(0));
    let live = Arc::new(AtomicUsize::new(0));
    let (pending, handing_over) = (Hold::new(), Hold::new());
    let pending_tid = Arc::new(AtomicUsize::new(usize::MAX));
    let finished = Arc::new(AtomicBool::new(false));

    let helpee = {
        let (closed, dropped, live) =
            (Arc::clone(&closed), Arc::clone(&dropped), Arc::clone(&live));
        let (pending, pending_tid, finished) = (
            pending.clone(),
            Arc::clone(&pending_tid),
            Arc::clone(&finished),
        );
        thread::spawn(move || {
            let tid = own_tid();
            // One batch of checkers into this thread's slot (the only
            // active one), moved to the free-list cache by a transition.
            {
                let _guard = pin();
                for _ in 0..RETIRE_FREQ {
                    let node = Box::into_raw(Box::new(ChecksOpen {
                        retired: RetiredNode::new(),
                        tid,
                        closed: Arc::clone(&closed),
                        dropped: Arc::clone(&dropped),
                    }));
                    unsafe { retire(node) };
                }
            }
            crate::slot::advance_epoch();
            drop(pin());
            // The next traversal frees the cache first.
            with_handle(|h| h.list_count.set(MAX_CACHE));
            // One more batch into the slot, for the slow path's loop to
            // traverse; no epoch advance on the way.
            with_handle(|h| h.alloc_counter.set(1));
            {
                let _guard = pin();
                for _ in 0..RETIRE_FREQ {
                    Counted::retire_one(&live);
                }
                // Publish the current epoch, as a protected load does, so
                // the helper's empty epoch transition closes the slot.
                let shared = crate::Atomic::<u64>::null();
                let _ = shared.load(Ordering::Acquire, &_guard);
            }
            pending_tid.store(tid, Ordering::SeqCst);
            pending.arm(Step::SlowPending, tid);
            // The transition, taken through its slow path, inside a pin.
            with_handle(|h| {
                h.pin_count.set(1);
                h.slow_path(0, tid);
                h.pin_count.set(0);
            });
            finished.store(true, Ordering::SeqCst);
        })
    };
    pending.reached("the pending thread");
    let pending_tid = pending_tid.load(Ordering::SeqCst);

    let helper = {
        let handing_over = handing_over.clone();
        thread::spawn(move || {
            let tid = own_tid();
            handing_over.arm(Step::EraClosed, tid);
            with_handle(|h| h.help_thread(pending_tid, 0, tid));
        })
    };
    handing_over.reached("the helper");
    let seqno = crate::slot::global().thread_slots(pending_tid).epoch[0].load_hi();
    assert_eq!(seqno & 1, 1, "the helper did not close the slot");

    // The pending thread completes while the helper stays held.
    pending.release();
    assert!(
        eventually(|| finished.load(Ordering::SeqCst)),
        "the slow path did not complete while its helper was held"
    );
    handing_over.release();
    join_within(helper, "the helper");
    join_within(helpee, "the pending thread");

    assert_eq!(dropped.load(Ordering::SeqCst), RETIRE_FREQ);
    assert_eq!(
        closed.load(Ordering::SeqCst),
        0,
        "destructors ran while their thread's slot was closed to new batches"
    );
    assert_eq!(live.load(Ordering::SeqCst), 0);
}

/// Taking a pending thread's slot list over ends however much other
/// threads retire meanwhile. The pending thread is stalled in its slow path
/// with an old epoch published, so a helper's empty epoch transition does
/// not close its slot; each time the helper has read the slot and is about
/// to empty it, another thread retires a batch of oldest-born values,
/// eligible for the pending slot while it takes new batches. The take must
/// close the slot first and then need one pass.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn list_hand_over_ends_while_retires_keep_coming() {
    /// Batches the retiring thread submits at most: one before the
    /// hand-over, then one per pass.
    const RETIRES: usize = 9;

    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));
    let global = crate::slot::global();

    // Places one batch of oldest-born values each time it is asked to, with
    // no advance after it, once its first retire is spent: an advance helps
    // the pending thread below, and one before the helper's would hand its
    // list over first.
    let (asked, answered) = (Arc::new(AtomicUsize::new(0)), Arc::new(AtomicUsize::new(0)));
    let started = Hold::new();
    let retirer = {
        let (asked, answered, live, started) = (
            Arc::clone(&asked),
            Arc::clone(&answered),
            Arc::clone(&live),
            started.clone(),
        );
        thread::spawn(move || {
            own_tid();
            spend_first_retire(&live);
            started.arrived.store(true, Ordering::SeqCst);
            for n in 1..=RETIRES {
                assert!(eventually(|| asked.load(Ordering::SeqCst) >= n));
                Counted::place_oldest(&live);
                answered.store(n, Ordering::SeqCst);
            }
        })
    };
    started.reached("the retiring thread");

    // A thread stalled in its slow path, publishing an epoch older than the
    // global one.
    crate::slot::advance_epoch();
    let pending = FakePending::open(crate::slot::epoch() - 1);
    let (pending_tid, slots) = (pending.tid, global.thread_slots(pending.tid));

    // A first batch, placed in the pending slot among others: the hand-over
    // has a list to take.
    asked.store(1, Ordering::SeqCst);
    assert!(eventually(|| answered.load(Ordering::SeqCst) >= 1));
    assert_ne!(
        slots.first[0].load_lo(),
        0,
        "the pending slot took no batch"
    );

    let passes = Arc::new(AtomicUsize::new(0));
    let helper = {
        let (asked, answered, passes) = (
            Arc::clone(&asked),
            Arc::clone(&answered),
            Arc::clone(&passes),
        );
        thread::spawn(move || {
            let tid = own_tid();
            stall::arm(Step::DetachList, tid, move || {
                let n = passes.fetch_add(1, Ordering::SeqCst) + 2;
                if n > RETIRES {
                    return false;
                }
                // Another thread's retire, between this read of the slot
                // and the attempt to empty it.
                asked.store(n, Ordering::SeqCst);
                assert!(eventually(|| answered.load(Ordering::SeqCst) >= n));
                true
            });
            with_handle(|h| h.help_thread(pending_tid, 0, tid));
        })
    };
    join_within(helper, "the helper");
    let passes = passes.load(Ordering::SeqCst);
    assert_eq!(
        passes, 1,
        "the hand-over took {passes} passes while another thread kept retiring"
    );

    // Let the retirer finish, then leave the pending thread's slot as an
    // exit would and free everything.
    asked.store(RETIRES, Ordering::SeqCst);
    join_within(retirer, "the retiring thread");
    join_within(
        thread::spawn(move || {
            own_tid();
            pending.finish();
        }),
        "the pending thread's exit",
    );
    drain(&live);
}

/// A protected load ends within its attempts whatever the epoch does:
/// another thread advancing the epoch between every pointer load and the
/// epoch read that should confirm it costs it `MAX_LOAD_ATTEMPTS - 1`
/// publications and one escalation, then one more load. The escalated
/// section ends in one transition at its guard's drop.
#[test]
fn protected_load_ends_within_its_attempts() {
    let _l = lock();
    join_within(
        thread::spawn(|| {
            let tid = own_tid();
            let passes = Arc::new(AtomicUsize::new(0));
            let p = Arc::clone(&passes);
            stall::arm(Step::LoadAttempt, tid, move || {
                p.fetch_add(1, Ordering::SeqCst);
                crate::slot::advance_epoch();
                true
            });
            let value = Box::into_raw(Box::new(7u64));
            let shared = crate::Atomic::new(value);
            let guard = pin();
            crate::slot::advance_epoch();
            let loaded = shared.load(Ordering::Acquire, &guard);
            stall::disarm(Step::LoadAttempt, tid);
            assert_eq!(loaded.as_raw(), value);
            assert_eq!(
                passes.load(Ordering::SeqCst),
                crate::guard::MAX_LOAD_ATTEMPTS - 1
            );
            assert_eq!(with_handle(|h| h.cached_epoch.get()), EPOCH_UNCONDITIONAL);
            drop(guard);
            assert_ne!(published_epoch(), EPOCH_UNCONDITIONAL);
            drop(unsafe { Box::from_raw(value) });
        }),
        "the loading thread",
    );
}

/// Runs `help_read` and then advances the epoch each time it is asked to,
/// as every epoch advance does: a thread that helps before it advances.
struct Advancer {
    asked: Arc<AtomicUsize>,
    answered: Arc<AtomicUsize>,
    stop: Arc<AtomicBool>,
    thread: thread::JoinHandle<()>,
}

impl Advancer {
    fn start() -> Self {
        let (asked, answered) = (Arc::new(AtomicUsize::new(0)), Arc::new(AtomicUsize::new(0)));
        let stop = Arc::new(AtomicBool::new(false));
        let thread = {
            let (asked, answered, stop) =
                (Arc::clone(&asked), Arc::clone(&answered), Arc::clone(&stop));
            thread::spawn(move || {
                let tid = own_tid();
                let mut done = 0;
                while eventually(|| {
                    stop.load(Ordering::SeqCst) || asked.load(Ordering::SeqCst) > done
                }) && !stop.load(Ordering::SeqCst)
                {
                    with_handle(|h| h.help_read(tid));
                    crate::slot::advance_epoch();
                    done += 1;
                    answered.store(done, Ordering::SeqCst);
                }
            })
        };
        Self {
            asked,
            answered,
            stop,
            thread,
        }
    }

    /// Help and advance once, on the advancer's thread; wait until done.
    fn help_and_advance(asked: &AtomicUsize, answered: &AtomicUsize) {
        let n = asked.fetch_add(1, Ordering::SeqCst) + 1;
        assert!(eventually(|| answered.load(Ordering::SeqCst) >= n));
    }

    fn stop(self) {
        self.stop.store(true, Ordering::SeqCst);
        join_within(self.thread, "the advancing thread");
    }
}

/// An outermost pin ends while the epoch moves at every attempt: its
/// transition makes 16 attempts, then its slow path passes once per epoch
/// advance made by a thread that did not see its help request (two here)
/// and ends at the first advance whose thread helped first, which
/// completes the request for it.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn pin_ends_while_the_epoch_moves_at_every_attempt() {
    const UNHELPED: usize = 2;
    let _l = lock();
    let advancer = Advancer::start();
    let (asked, answered) = (Arc::clone(&advancer.asked), Arc::clone(&advancer.answered));
    let (attempts, passes) = (Arc::new(AtomicUsize::new(0)), Arc::new(AtomicUsize::new(0)));
    let (a, p) = (Arc::clone(&attempts), Arc::clone(&passes));
    join_within(
        thread::spawn(move || {
            let tid = own_tid();
            stall::arm(Step::TransitionAttempt, tid, move || {
                a.fetch_add(1, Ordering::SeqCst);
                crate::slot::advance_epoch();
                true
            });
            stall::arm(Step::SlowPass, tid, move || {
                let n = p.fetch_add(1, Ordering::SeqCst) + 1;
                if n <= UNHELPED {
                    crate::slot::advance_epoch();
                } else {
                    Advancer::help_and_advance(&asked, &answered);
                }
                true
            });
            crate::slot::advance_epoch();
            drop(pin());
            stall::disarm(Step::TransitionAttempt, tid);
            stall::disarm(Step::SlowPass, tid);
        }),
        "the pinning thread",
    );
    advancer.stop();
    assert_eq!(attempts.load(Ordering::SeqCst), 16);
    assert_eq!(passes.load(Ordering::SeqCst), UNHELPED + 1);
}

/// A retire's insert held between exchanging its node into another
/// thread's slot and linking the list it displaced keeps no one waiting:
/// the slot's owner transitions (its traversal ends at the unlinked node),
/// and a third thread retires into the same slot. Let go, the insert finds
/// the list taken and walks the rest itself; everything is freed once.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn pin_and_retire_end_while_an_insert_is_held() {
    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));

    // The slot owner, with a lower ID than the inserter: the inserter's
    // scan reaches its slot first. One batch already in its slot.
    let (owner_up, owner_go) = (Hold::new(), Hold::new());
    let owner_pinned = Arc::new(AtomicBool::new(false));
    let owner_tid = Arc::new(AtomicUsize::new(0));
    let owner = {
        let (up, go, live, pinned, owner_tid) = (
            owner_up.clone(),
            owner_go.clone(),
            Arc::clone(&live),
            Arc::clone(&owner_pinned),
            Arc::clone(&owner_tid),
        );
        thread::spawn(move || {
            owner_tid.store(own_tid(), Ordering::SeqCst);
            for _ in 0..RETIRE_FREQ {
                Counted::retire_oldest(&live);
            }
            up.arrived.store(true, Ordering::SeqCst);
            assert!(eventually(|| go.go.load(Ordering::SeqCst)));
            // A transition: take the list whose head is the held insert.
            crate::slot::advance_epoch();
            drop(pin());
            pinned.store(true, Ordering::SeqCst);
            assert!(eventually(|| go.arrived.load(Ordering::SeqCst)));
        })
    };
    owner_up.reached("the slot owner");

    let inserting = Hold::new();
    let inserter = {
        let (inserting, live) = (inserting.clone(), Arc::clone(&live));
        thread::spawn(move || {
            let tid = own_tid();
            inserting.arm(Step::InsertExchanged, tid);
            for _ in 0..RETIRE_FREQ {
                Counted::retire_oldest(&live);
            }
        })
    };
    inserting.reached("the inserting thread");
    assert!(head_is_unlinked(owner_tid.load(Ordering::SeqCst)));

    // While it is held: the owner transitions, a third thread retires.
    owner_go.release();
    assert!(
        eventually(|| owner_pinned.load(Ordering::SeqCst)),
        "the slot owner's pin did not complete while an insert into its slot was held"
    );
    let third = {
        let live = Arc::clone(&live);
        thread::spawn(move || {
            own_tid();
            for _ in 0..RETIRE_FREQ {
                Counted::retire_oldest(&live);
            }
        })
    };
    join_within(third, "a retire into the same slot");

    inserting.release();
    join_within(inserter, "the held retire");
    owner_go.arrived.store(true, Ordering::SeqCst);
    join_within(owner, "the slot owner");
    drain(&live);
}

/// A traversal walks the list its exchange captured and no more: held
/// after the capture while another thread retires batch after batch into
/// the same slot, the transition, let go, frees exactly the batches it
/// captured, and every entry inserted meanwhile is still in the slot.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn traversal_walks_only_the_list_it_captured() {
    const CAPTURED: usize = 4;
    const INSERTED: usize = 8;
    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));
    let traversing = Hold::new();
    let (traversed, owner_tid) = (
        Arc::new(AtomicBool::new(false)),
        Arc::new(AtomicUsize::new(0)),
    );
    let checked = Hold::new();
    let owner = {
        let (traversing, traversed, owner_tid, checked, live) = (
            traversing.clone(),
            Arc::clone(&traversed),
            Arc::clone(&owner_tid),
            checked.clone(),
            Arc::clone(&live),
        );
        thread::spawn(move || {
            let tid = own_tid();
            owner_tid.store(tid, Ordering::SeqCst);
            // Batches whose one slot is this thread's (the only one
            // active; oldest-born values, so its epoch covers them however
            // the epoch moves meanwhile): the list the transition below
            // captures.
            for _ in 0..CAPTURED * RETIRE_FREQ {
                Counted::retire_oldest(&live);
            }
            with_handle(|h| h.list_count.set(0));
            traversing.arm(Step::Traverse, tid);
            crate::slot::advance_epoch();
            drop(pin());
            traversed.store(true, Ordering::SeqCst);
            // What the traversal freed waits in the cache: one traversal,
            // the captured batches, released at the next flush or when the
            // cache fills.
            let (traversals, freed) = with_handle(|h| {
                let mut n = 0;
                let mut refs = h.free_list.get();
                while !refs.is_null() {
                    n += 1;
                    refs = unsafe { (*refs).next.load(Ordering::Relaxed) };
                }
                (h.list_count.get(), n)
            });
            assert_eq!((traversals, freed), (1, CAPTURED));
            assert!(eventually(|| checked.go.load(Ordering::SeqCst)));
        })
    };
    traversing.reached("the traversing thread");
    let owner_tid = owner_tid.load(Ordering::SeqCst);

    // Another thread retires batches of oldest-born values: each takes an
    // entry in the held thread's slot.
    let retirer = {
        let live = Arc::clone(&live);
        thread::spawn(move || {
            own_tid();
            for _ in 0..INSERTED * RETIRE_FREQ {
                Counted::retire_oldest(&live);
            }
        })
    };
    join_within(retirer, "the retiring thread");
    traversing.release();
    assert!(eventually(|| traversed.load(Ordering::SeqCst)));

    // Every entry inserted during the traversal is still in the slot.
    let mut in_slot = 0;
    let mut at =
        crate::slot::global().thread_slots(owner_tid).first[0].load_lo() as *mut RetiredNode;
    while !at.is_null() && at as usize != crate::retired::INVPTR {
        in_slot += 1;
        at = unsafe { (*at).next.load(Ordering::Acquire) };
    }
    assert_eq!(
        in_slot, INSERTED,
        "the traversal consumed entries inserted after its capture"
    );
    checked.release();
    join_within(owner, "the traversing thread");
    drain(&live);
}

/// The drop that ends an escalated section is one transition, and it waits
/// for no one: a thread stalled in its slow path for good and a retire held
/// mid insert into the escalated thread's slot do not delay it.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn escalated_drop_ends_while_others_are_held() {
    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));

    // The escalating thread, with the lowest ID: the insert lands in its
    // slot first.
    let (escalated, go) = (Hold::new(), Hold::new());
    let dropped = Arc::new(AtomicBool::new(false));
    let section_tid = Arc::new(AtomicUsize::new(0));
    let section = {
        let (escalated, go, dropped, section_tid) = (
            escalated.clone(),
            go.clone(),
            Arc::clone(&dropped),
            Arc::clone(&section_tid),
        );
        thread::spawn(move || {
            section_tid.store(own_tid(), Ordering::SeqCst);
            let guard = pin();
            with_handle(|h| h.escalate());
            escalated.arrived.store(true, Ordering::SeqCst);
            assert!(eventually(|| go.go.load(Ordering::SeqCst)));
            drop(guard);
            assert_ne!(published_epoch(), EPOCH_UNCONDITIONAL);
            dropped.store(true, Ordering::SeqCst);
            assert!(eventually(|| go.arrived.load(Ordering::SeqCst)));
        })
    };
    escalated.reached("the escalating thread");
    let pending = FakePending::open(crate::slot::epoch());

    let inserting = Hold::new();
    let inserter = {
        let (inserting, live) = (inserting.clone(), Arc::clone(&live));
        thread::spawn(move || {
            let tid = own_tid();
            inserting.arm(Step::InsertExchanged, tid);
            for _ in 0..RETIRE_FREQ {
                Counted::retire_oldest(&live);
            }
        })
    };
    inserting.reached("the inserting thread");
    assert!(head_is_unlinked(section_tid.load(Ordering::SeqCst)));

    go.release();
    assert!(
        eventually(|| dropped.load(Ordering::SeqCst)),
        "the escalated drop did not complete while others were held"
    );
    inserting.release();
    join_within(inserter, "the held retire");
    go.arrived.store(true, Ordering::SeqCst);
    join_within(section, "the escalating thread");
    join_within(
        thread::spawn(move || {
            own_tid();
            pending.finish();
        }),
        "the pending thread's exit",
    );
    drain(&live);
}

/// flush() waits for no one either: with a thread stalled in its slow path
/// for good (flush helps it, completing its request), a traversal held
/// after its capture and a retire held mid insert, a flushing thread
/// submits, adopts, helps, advances and frees, and returns.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn flush_ends_while_others_are_held() {
    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));
    let pending = FakePending::open(crate::slot::epoch());
    let pending_tid = pending.tid;

    let traversing = Hold::new();
    let traverser = {
        let (traversing, live) = (traversing.clone(), Arc::clone(&live));
        thread::spawn(move || {
            let tid = own_tid();
            for _ in 0..RETIRE_FREQ {
                Counted::retire_one(&live);
            }
            traversing.arm(Step::Traverse, tid);
            crate::slot::advance_epoch();
            drop(pin());
        })
    };
    traversing.reached("the traversing thread");

    let inserting = Hold::new();
    let inserter = {
        let (inserting, live) = (inserting.clone(), Arc::clone(&live));
        thread::spawn(move || {
            let tid = own_tid();
            inserting.arm(Step::InsertExchanged, tid);
            for _ in 0..RETIRE_FREQ {
                Counted::retire_oldest(&live);
            }
        })
    };
    inserting.reached("the inserting thread");

    let flusher = {
        let live = Arc::clone(&live);
        thread::spawn(move || {
            own_tid();
            for _ in 0..RETIRE_FREQ / 2 {
                Counted::retire_oldest(&live);
            }
            flush();
        })
    };
    join_within(flusher, "a flush while others are held");
    let result = crate::slot::global().thread_slots(pending_tid).state[0]
        .result
        .load_lo();
    assert_ne!(
        result,
        crate::retired::INVPTR as u64,
        "the flush did not complete the stalled thread's request"
    );

    traversing.release();
    join_within(traverser, "the held traversal");
    inserting.release();
    join_within(inserter, "the held retire");
    join_within(
        thread::spawn(move || {
            own_tid();
            pending.finish();
        }),
        "the pending thread's exit",
    );
    drain(&live);
}

/// A helper stays with the request it started helping: once that request
/// is answered, even if the pending thread opens its next one at once, the
/// helper's loop ends. Following the thread into its next request would let
/// epoch advances made for that one keep the helper looping.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn help_ends_when_its_request_changes() {
    let _l = lock();
    let mut pending = FakePending::open(crate::slot::epoch());
    let (pending_tid, seqno) = (pending.tid, pending.seqno);
    let passes = Arc::new(AtomicUsize::new(0));
    let p = Arc::clone(&passes);
    join_within(
        thread::spawn(move || {
            let tid = own_tid();
            stall::arm(Step::HelpPass, tid, move || {
                if p.fetch_add(1, Ordering::SeqCst) == 0 {
                    // During the first pass the epoch moves, another helper
                    // answers the request, and the pending thread ends that
                    // cycle and opens its next request.
                    crate::slot::advance_epoch();
                    let slots = crate::slot::global().thread_slots(pending_tid);
                    let result = &slots.state[0].result;
                    result.store(0, crate::slot::epoch(), Ordering::SeqCst);
                    slots.epoch[0].store_hi(seqno + 2, Ordering::SeqCst);
                    slots.first[0].store_hi(seqno + 2, Ordering::SeqCst);
                    result.store(crate::retired::INVPTR as u64, seqno + 2, Ordering::SeqCst);
                }
                true
            });
            with_handle(|h| h.help_thread(pending_tid, 0, tid));
            stall::disarm(Step::HelpPass, tid);
        }),
        "the helper",
    );
    assert_eq!(passes.load(Ordering::SeqCst), 1);
    let result = crate::slot::global().thread_slots(pending_tid).state[0]
        .result
        .load();
    assert_eq!(
        result,
        (crate::retired::INVPTR as u64, seqno + 2),
        "the helper answered a later request than the one it was helping"
    );
    pending.seqno += 2;
    join_within(
        thread::spawn(move || {
            own_tid();
            pending.finish();
        }),
        "the pending thread's exit",
    );
}

/// A helper's loop ends with the cycle of the request it helps, even when
/// its check of that request reads the request's two words across two
/// cycles. The helper reads a thread's first request, `(INVPTR, 0)`. During
/// each of its passes the epoch moves, the thread self-completes its current
/// request and opens its next one, and between the two halves of the
/// helper's check the thread self-completes that one too: the check reads a
/// later request's INVPTR and the 0 its self-completion leaves, the pair
/// the helper started with. The loop still passes at most T + 2 times.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn help_ends_with_its_cycle_across_a_torn_request_read() {
    let _l = lock();
    // The pending thread: an ID whose slot never took a slow path, so its
    // first request has seqno 0. IDs whose slots did are held meanwhile.
    let mut others = std::vec::Vec::new();
    let mut pending = loop {
        let p = FakePending::open(crate::slot::epoch());
        if p.seqno == 0 {
            break p;
        }
        others.push(p);
    };
    let pending_tid = pending.tid;
    // The era's seqno the pending thread's cycles leave, the helper's passes
    // and their bound, T + 2 with T the IDs handed out.
    let era = Arc::new(AtomicUsize::new(0));
    let passes = Arc::new(AtomicUsize::new(0));
    let bound = Arc::new(AtomicUsize::new(0));
    let (e, p) = (Arc::clone(&era), Arc::clone(&passes));
    let (e2, p2, b) = (Arc::clone(&era), Arc::clone(&passes), Arc::clone(&bound));
    join_within(
        thread::spawn(move || {
            let tid = own_tid();
            b.store(crate::slot::global().max_threads() + 2, Ordering::SeqCst);
            // One cycle of the pending thread per pass, for more passes than
            // the bound allows.
            let cycles = b.load(Ordering::SeqCst) + 2;
            let slots = crate::slot::global().thread_slots(pending_tid);
            let result = &slots.state[0].result;
            let inv = crate::retired::INVPTR as u64;
            // The pending thread ends the cycle it is in: a self-completion.
            let self_complete = move |era: &AtomicUsize| {
                let seqno = era.load(Ordering::SeqCst) as u64;
                assert!(result.compare_exchange(inv, seqno, 0, 0).is_ok());
                slots.epoch[0].store_hi(seqno + 2, Ordering::SeqCst);
                slots.first[0].store_hi(seqno + 2, Ordering::SeqCst);
                era.store(seqno as usize + 2, Ordering::SeqCst);
            };
            stall::arm(Step::HelpPass, tid, move || {
                let pass = p.fetch_add(1, Ordering::SeqCst);
                if pass < cycles {
                    // The first request ends; after that, none is open.
                    if pass == 0 {
                        self_complete(&e);
                    }
                    // The pending thread opens its next request, and the
                    // epoch moves during this pass.
                    result.store(inv, e.load(Ordering::SeqCst) as u64, Ordering::SeqCst);
                    crate::slot::advance_epoch();
                }
                true
            });
            stall::arm(Step::HelpRecheck, tid, move || {
                // The request just opened ends between the check's two
                // loads: the low word read was its INVPTR, the high word
                // read is its self-completion's 0.
                if p2.load(Ordering::SeqCst) <= cycles {
                    self_complete(&e2);
                }
                true
            });
            with_handle(|h| h.help_thread(pending_tid, 0, tid));
            stall::disarm(Step::HelpPass, tid);
            stall::disarm(Step::HelpRecheck, tid);
        }),
        "the helper",
    );
    let (passes, bound) = (passes.load(Ordering::SeqCst), bound.load(Ordering::SeqCst));
    assert!(
        passes <= bound,
        "the helper made {passes} passes, more than T + 2 = {bound}: it followed the pending \
         thread through later cycles"
    );
    let slots = crate::slot::global().thread_slots(pending_tid);
    assert_eq!(slots.state[0].result.load().0, 0, "a request was left open");
    pending.seqno = era.load(Ordering::SeqCst) as u64;
    join_within(
        thread::spawn(move || {
            own_tid();
            pending.finish();
            for other in others {
                other.finish();
            }
        }),
        "the pending threads' exits",
    );
}

/// An insert that finds its slot deactivated when it exchanges its node in
/// (the owner exited after the scan found the slot eligible) takes the node
/// back out with one compare-exchange of the list word, and the slot is
/// inactive again: it holds no node of the batch, which is freed.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn insert_into_an_exited_slot_rolls_back() {
    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));

    // The slot owner, with the lower ID: the insert targets its slot first.
    let (owner_up, owner_exit) = (Hold::new(), Hold::new());
    let owner_tid = Arc::new(AtomicUsize::new(0));
    let owner = {
        let (up, exit, owner_tid) = (owner_up.clone(), owner_exit.clone(), Arc::clone(&owner_tid));
        thread::spawn(move || {
            owner_tid.store(own_tid(), Ordering::SeqCst);
            up.arrived.store(true, Ordering::SeqCst);
            assert!(eventually(|| exit.go.load(Ordering::SeqCst)));
        })
    };
    owner_up.reached("the slot owner");
    let owner_tid = owner_tid.load(Ordering::SeqCst);

    let ready = Hold::new();
    let inserter = {
        let (ready, live) = (ready.clone(), Arc::clone(&live));
        thread::spawn(move || {
            let tid = own_tid();
            ready.arm(Step::InsertReady, tid);
            for _ in 0..RETIRE_FREQ {
                Counted::retire_oldest(&live);
            }
        })
    };
    ready.reached("the inserting thread");

    // The owner exits while the insert is held after its checks.
    owner_exit.release();
    join_within(owner, "the slot owner's exit");
    let slot = &crate::slot::global().thread_slots(owner_tid).first[0];
    assert_eq!(slot.load_lo(), crate::retired::INVPTR as u64);

    ready.release();
    join_within(inserter, "the insert");
    assert_eq!(
        slot.load_lo(),
        crate::retired::INVPTR as u64,
        "the exited slot kept the node an insert put into it"
    );
    drain(&live);
}

/// One retired batch takes a node in the retiring thread's own helper slot
/// when that slot is active and publishes an era at or above the batch's
/// birth epoch. The test sets that state with the `do_update` a help runs at
/// its HelpPass step, then reads every slot list that holds a node of the
/// batch: a published node's `next` is its list link, so the lists are the
/// evidence of where placement put it.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn batch_placement_includes_the_helper_slot() {
    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));

    // Pinned in a loop and never flushed: its reservation slot stays active,
    // so the batch takes a node there too.
    let (up, stop) = (Hold::new(), Hold::new());
    let reader_tid = Arc::new(AtomicUsize::new(0));
    let reader = {
        let (up, stop, reader_tid) = (up.clone(), stop.clone(), Arc::clone(&reader_tid));
        thread::spawn(move || {
            reader_tid.store(own_tid(), Ordering::SeqCst);
            drop(pin());
            up.arrived.store(true, Ordering::SeqCst);
            while !stop.go.load(Ordering::SeqCst) {
                drop(pin());
                thread::yield_now();
            }
        })
    };
    up.reached("the reader");

    // The helper slot a help publishes before its passes: active, publishing
    // the current era. Nothing else activates it, `state.parent` staying 0.
    let tid = own_tid();
    let global = crate::slot::global();
    let hr_num = global.hr_num();
    with_handle(|h| h.do_update(crate::slot::epoch(), hr_num + 1, tid));

    // One batch of oldest-born values, finalized and placed: a node in every
    // active slot whose era covers it.
    let mut nodes = std::vec::Vec::new();
    for _ in 0..RETIRE_FREQ - 1 {
        live.fetch_add(1, Ordering::SeqCst);
        let retired = RetiredNode::new();
        retired.set_birth_epoch(1);
        let node = Box::into_raw(Box::new(Counted {
            retired,
            live: Arc::clone(&live),
        }));
        nodes.push(node as usize);
        unsafe { retire(node) };
    }
    with_handle(|h| {
        let (first, last) = h.take_batch().expect("the batch just retired");
        assert!(h.try_retire(first, last, None), "the batch was not placed");
    });

    // Every slot list whose head is one of the batch's nodes: the scan
    // assigns one node per eligible slot, so each of these heads is one.
    let mut placed = std::vec::Vec::new();
    for i in 0..global.max_threads() {
        let slots = global.thread_slots(i);
        for (j, word) in slots.first.iter().enumerate() {
            let head = word.load_lo() as usize;
            if head != 0 && head != crate::retired::INVPTR && nodes.contains(&head) {
                placed.push((i, j));
            }
        }
    }
    // Both reservation slots and this thread's helper slot: the parent slot
    // stays inactive, so the batch takes nothing there.
    let mut expected = std::vec![
        (reader_tid.load(Ordering::SeqCst), 0),
        (tid, 0),
        (tid, hr_num + 1)
    ];
    expected.sort();
    placed.sort();
    assert_eq!(
        placed, expected,
        "placement put the batch's nodes in other slot lists"
    );

    // Leave the batch as a help's next pass leaves it: the reservation and
    // the helper lists traversed, then the batches they released freed.
    stop.go.store(true, Ordering::SeqCst);
    join_within(reader, "the reader");
    with_handle(|h| h.do_update(crate::slot::epoch(), hr_num + 1, tid));
    crate::slot::advance_epoch();
    drop(pin());
    with_handle(|h| h.drain_free_list());
    assert_eq!(
        live.load(Ordering::SeqCst),
        0,
        "the batch was not freed once every slot that took a node was traversed"
    );
}

/// A node a batch takes in a thread's helper slot is released by that
/// thread's own transition: the helper slot is one more list the transition
/// has to traverse, and a batch completes only once every slot holding one
/// of its nodes has been traversed. The reader keeps its own slot moving, so
/// the helper slot is the only list left holding the batch back, and the
/// count reaches zero once it is traversed.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn a_helper_slot_node_is_released_by_its_owners_transition() {
    /// Lets the reader go when the test unwinds, so a failed assertion ends
    /// its loop.
    struct LetGo(Hold);

    impl Drop for LetGo {
        fn drop(&mut self) {
            self.0.release();
        }
    }

    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));

    // Pins and drops in a loop and never flushes: its slot takes a node of
    // the batch and traverses it on a later pin.
    let (up, stop) = (Hold::new(), Hold::new());
    let reader = {
        let (up, stop) = (up.clone(), stop.clone());
        thread::spawn(move || {
            own_tid();
            drop(pin());
            up.arrived.store(true, Ordering::SeqCst);
            while !stop.go.load(Ordering::SeqCst) {
                drop(pin());
                thread::yield_now();
            }
        })
    };
    up.reached("the reader");
    let _let_go = LetGo(stop.clone());

    // This thread's helper slot, active at the current era, as a help leaves
    // it before its passes.
    let tid = own_tid();
    let hr_num = crate::slot::global().hr_num();
    with_handle(|h| h.do_update(crate::slot::epoch(), hr_num + 1, tid));

    // One batch of oldest-born values, taking a node in the reader's slot and
    // in both of this thread's active slots.
    Counted::place_oldest(&live);
    let global = crate::slot::global();
    let helper = global.thread_slots(tid).first[hr_num + 1].load_lo();
    assert!(
        helper != 0 && helper != crate::retired::INVPTR as u64,
        "the helper slot took no node"
    );

    // A transition on this thread, with the epoch moved so the next pin runs
    // one: it traverses the reservation slot and takes the helper slot.
    let drained = Arc::new(AtomicBool::new(false));
    {
        let drained = Arc::clone(&drained);
        stall::arm(Step::HelperDrain, tid, move || {
            drained.store(true, Ordering::SeqCst);
            false
        });
    }
    crate::slot::advance_epoch();
    drop(pin());
    assert!(
        drained.load(Ordering::SeqCst),
        "the transition did not reach the helper slot"
    );
    assert_eq!(
        crate::slot::global().thread_slots(tid).first[hr_num + 1].load_lo(),
        0,
        "the helper slot still holds a node after its owner's transition"
    );
    assert_eq!(
        global.thread_slots(tid).first[0].load_lo(),
        0,
        "the reservation slot still holds a node"
    );
    // The reader's next pin traverses its own slot. What that released waits
    // in its cache, so the batch ends once the thread that freed it flushes,
    // which its exit does.
    stop.release();
    join_within(reader, "the reader");
    with_handle(|h| h.drain_free_list());
    assert_eq!(
        live.load(Ordering::SeqCst),
        0,
        "the batch was not freed after the helper slot's node was released"
    );
}

/// A drain held between reading a helper slot and emptying it waits for no
/// one: another thread retires a batch into the same slot, so the take either
/// captures both nodes or leaves the displaced list to the insert's link. The
/// owner ends its transition, and every value is freed exactly once.
#[test]
#[cfg_attr(miri, ignore)] // multi-threaded: hits the intentional mixed-size DCAS, outside Miri's model
fn drain_takes_a_list_an_insert_joins() {
    let _l = lock();
    let live = Arc::new(AtomicUsize::new(0));

    // The draining thread: its helper slot active at the current era, and a
    // transition that finds the batch below in it.
    let (ready, go) = (Hold::new(), Hold::new());
    let parking = Hold::new();
    let drainer = {
        let (ready, go, parking) = (ready.clone(), go.clone(), parking.clone());
        thread::spawn(move || {
            let tid = own_tid();
            let hr_num = crate::slot::global().hr_num();
            with_handle(|h| h.do_update(crate::slot::epoch(), hr_num + 1, tid));
            ready.arrived.store(true, Ordering::SeqCst);
            assert!(eventually(|| go.go.load(Ordering::SeqCst)));
            parking.arm(Step::DetachList, tid);
            crate::slot::advance_epoch();
            drop(pin());
        })
    };
    ready.reached("the draining thread");

    // A batch in every active slot, the draining thread's helper slot among
    // them: the list its drain reads.
    Counted::place_oldest(&live);
    go.release();
    parking.reached("the drain");

    // While the drain is held: another retire takes the same slot.
    Counted::place_oldest(&live);
    parking.release();
    join_within(drainer, "the draining thread");
    drain(&live);
}
