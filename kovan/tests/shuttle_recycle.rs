//! Shuttle model-checked test for node recycling: a node a guard has loaded
//! is not handed back to the pool, and so not rewritten, until that guard
//! drops.
//!
//! A pool-backed node type overrides `Reclaimable::dealloc` to poison its
//! value and push the node on a free list; the writer takes nodes back from
//! that list (re-arming the header, as `Reclaimable` documents) instead of
//! allocating. One reader pins a guard, loads the published node and reads it
//! twice with yield points between; the writer meanwhile swaps in new nodes,
//! retires the old ones with `retire_reclaimable` and reuses whatever the pool
//! gives back, flushing after each. If kovan ever called `dealloc` on a node
//! while that guard could still see it, the node would be poisoned, or
//! rewritten by the writer's next reuse, and the reader's second read would
//! differ from its first.
//!
//! The books are checked as well, as `shuttle_reclaim.rs` does: once the
//! tasks finish and every thread has flushed, each node allocated must be in
//! the pool exactly once and `dealloc` must have run once per incarnation. A
//! node reclaimed twice, or never, shows up there.
//!
//! The pool is a `shuttle::sync::Mutex` so the scheduler also explores the
//! interleavings around `dealloc`, which runs on whichever task frees the
//! batch. See `shuttle_reclaim.rs` for why the `shuttle` feature and the
//! per-task thread-local `Handle` matter, and how to replay a failure.

#![cfg(feature = "shuttle")]

use kovan::{Atomic, Reclaimable, RetiredNode, Shared, flush, pin, retire_reclaimable};
use shuttle::sync::Mutex;
use std::collections::HashSet;
use std::ptr;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

const POISON: u64 = u64::MAX;
const KEY: u64 = 0x9E37_79B9_7F4A_7C15;

struct Ptr(*mut Slot);

// SAFETY: a pooled node is reachable only through the pool.
unsafe impl Send for Ptr {}

struct Pool {
    free: Mutex<Vec<Ptr>>,
    allocs: AtomicUsize,
    acquires: AtomicUsize,
    deallocs: AtomicUsize,
}

impl Pool {
    fn leak() -> &'static Pool {
        Box::leak(Box::new(Pool {
            free: Mutex::new(Vec::new()),
            allocs: AtomicUsize::new(0),
            acquires: AtomicUsize::new(0),
            deallocs: AtomicUsize::new(0),
        }))
    }

    /// A node holding `seq`: recycled if the pool has one, allocated if not.
    fn acquire(&'static self, seq: u64) -> *mut Slot {
        self.acquires.fetch_add(1, Ordering::SeqCst);
        let recycled = self.free.lock().unwrap().pop().map(|p| p.0);
        let node = match recycled {
            Some(node) => {
                // SAFETY: the node left the pool, so this task owns it. The
                // header is re-armed before the node can be published.
                unsafe { ptr::write(&raw mut (*node).retired, RetiredNode::new()) };
                node
            }
            None => {
                self.allocs.fetch_add(1, Ordering::SeqCst);
                Box::into_raw(Box::new(Slot {
                    retired: RetiredNode::new(),
                    seq: AtomicU64::new(0),
                    echo: AtomicU64::new(0),
                    pool: self,
                }))
            }
        };
        // SAFETY: unpublished, so no other task reads it yet.
        unsafe { (*node).fill(seq) };
        node
    }
}

#[repr(C)]
struct Slot {
    retired: RetiredNode,
    seq: AtomicU64,
    echo: AtomicU64,
    pool: &'static Pool,
}

impl Slot {
    fn fill(&self, seq: u64) {
        self.seq.store(seq, Ordering::SeqCst);
        self.echo.store(seq ^ KEY, Ordering::SeqCst);
    }

    /// The sequence number, after checking the value is whole and not poisoned.
    fn check(&self) -> u64 {
        let seq = self.seq.load(Ordering::SeqCst);
        assert_ne!(seq, POISON, "reader saw a node already passed to dealloc");
        assert_eq!(
            self.echo.load(Ordering::SeqCst),
            seq ^ KEY,
            "reader saw a torn or recycled value for seq {seq}"
        );
        seq
    }
}

// SAFETY: `RetiredNode` is the first field of a `#[repr(C)]` struct.
unsafe impl Reclaimable for Slot {
    fn retired_node(&self) -> &RetiredNode {
        &self.retired
    }

    fn retired_node_mut(&mut self) -> &mut RetiredNode {
        &mut self.retired
    }

    unsafe fn dealloc(node: *mut Self) {
        // SAFETY: kovan never touches the node again and no guard reaches it,
        // so it is ours to poison and hand to the pool.
        unsafe {
            let pool = (*node).pool;
            (*node).seq.store(POISON, Ordering::SeqCst);
            (*node).echo.store(POISON, Ordering::SeqCst);
            pool.deallocs.fetch_add(1, Ordering::SeqCst);
            pool.free.lock().unwrap().push(Ptr(node));
        }
    }
}

/// Swap in a fresh node holding `seq` and retire what it replaced.
fn publish(pool: &'static Pool, slot: &Atomic<Slot>, seq: u64) {
    let node = pool.acquire(seq);
    let guard = pin();
    // SAFETY: `node` is unpublished and valid; `old` is unlinked by the swap.
    let old = slot.swap(unsafe { Shared::from_raw(node) }, Ordering::AcqRel, &guard);
    if !old.is_null() {
        // SAFETY: retired once, never touched again by this task.
        unsafe { retire_reclaimable(old.as_raw()) };
    }
}

fn recycle_while_protected() {
    let pool = Pool::leak();
    let slot = Arc::new(Atomic::new(pool.acquire(1)));

    let reader = {
        let slot = Arc::clone(&slot);
        shuttle::thread::spawn(move || {
            let guard = pin();
            let shared = slot.load(Ordering::Acquire, &guard);
            // SAFETY: loaded under `guard`, which stays live below.
            if let Some(node) = unsafe { shared.as_ref() } {
                let seq = node.check();
                // Hold the guard while the writer retires and reuses nodes.
                shuttle::thread::yield_now();
                assert_eq!(node.check(), seq, "value changed under a live guard");
                shuttle::thread::yield_now();
                assert_eq!(node.check(), seq, "value changed under a live guard");
            }
            drop(guard);
            // A batch retired meanwhile may sit in this task's slot, and only
            // the owner can drain it (see `shuttle_reclaim.rs`).
            flush();
        })
    };
    let writer = {
        let slot = Arc::clone(&slot);
        shuttle::thread::spawn(move || {
            // Each round retires the node before it and takes the next from
            // the pool, which holds the earlier ones once they are reclaimed.
            for seq in 2..=4 {
                publish(pool, &slot, seq);
                flush();
            }
        })
    };

    reader.join().unwrap();
    writer.join().unwrap();

    // Retire the node still published, then drain what the tasks left.
    {
        let guard = pin();
        // SAFETY: a null `Shared` is valid for `swap`.
        let last = slot.swap(
            unsafe { Shared::from_raw(ptr::null_mut()) },
            Ordering::AcqRel,
            &guard,
        );
        // SAFETY: retired once, never touched again.
        unsafe { retire_reclaimable(last.as_raw()) };
    }
    for _ in 0..8 {
        flush();
    }

    let allocs = pool.allocs.load(Ordering::SeqCst);
    let acquires = pool.acquires.load(Ordering::SeqCst);
    let deallocs = pool.deallocs.load(Ordering::SeqCst);
    let mut free = pool.free.lock().unwrap();
    let distinct: HashSet<usize> = free.iter().map(|p| p.0 as usize).collect();
    assert_eq!(
        deallocs, acquires,
        "dealloc must run once per incarnation: {acquires} acquired, {deallocs} deallocated"
    );
    assert_eq!(distinct.len(), free.len(), "a node was pooled twice");
    assert_eq!(free.len(), allocs, "a retired node never came back");
    for Ptr(node) in free.drain(..) {
        // SAFETY: allocated by `acquire` with `Box`, owned by the pool.
        drop(unsafe { Box::from_raw(node) });
    }
}

#[test]
fn shuttle_recycle_while_protected() {
    shuttle::check_pct(recycle_while_protected, 5000, 5);
}
