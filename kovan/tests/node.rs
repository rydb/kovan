//! The node helpers (`alloc_node`, `retire_node`, `drop_node`, `free_node`,
//! `alloc_node_uninit`), with and without the `recycle` feature. A counting
//! global allocator tells whether a steady state still calls into the
//! global allocator.

use kovan::{
    Atomic, RetiredNode, Shared, alloc_node, alloc_node_uninit, drop_node, flush, free_node, pin,
    retire_node,
};
use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Counts the allocations of the thread that turned counting on.
struct Counting;

thread_local! {
    static COUNTING: Cell<bool> = const { Cell::new(false) };
    static ALLOCS: Cell<usize> = const { Cell::new(0) };
}

// SAFETY: forwards every call to `System`; the counters are thread-local
// cells, touched without allocating.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let _ = COUNTING.try_with(|on| {
            if on.get() {
                ALLOCS.with(|n| n.set(n.get() + 1));
            }
        });
        // SAFETY: forwarded.
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: forwarded.
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static GLOBAL: Counting = Counting;

/// The allocations `f` makes on this thread.
fn allocations_of(f: impl FnOnce()) -> usize {
    ALLOCS.with(|n| n.set(0));
    COUNTING.with(|on| on.set(true));
    f();
    COUNTING.with(|on| on.set(false));
    ALLOCS.with(|n| n.get())
}

#[repr(C)]
struct Node {
    retired: RetiredNode,
    value: u64,
}

fn node(value: u64) -> *mut Node {
    alloc_node(Node {
        retired: RetiredNode::new(),
        value,
    })
}

#[test]
fn drop_node_and_alloc_node_reach_a_steady_state() {
    // Warm up: the first round fills this thread's magazines.
    for i in 0..100 {
        // SAFETY: a fresh node no other thread reaches.
        unsafe { drop_node(node(i)) };
    }
    let n = allocations_of(|| {
        for i in 0..10_000 {
            // SAFETY: as above.
            unsafe { drop_node(node(i)) };
        }
    });
    if cfg!(feature = "recycle") {
        assert_eq!(
            n, 0,
            "the cache should serve every node of the steady state"
        );
    } else {
        assert_eq!(n, 10_000, "without the cache every node is a Box");
    }
}

#[test]
fn a_freed_node_memory_is_reused_for_the_next_node() {
    let a = node(1);
    // SAFETY: a fresh node no other thread reaches.
    unsafe { drop_node(a) };
    let b = node(2);
    if cfg!(feature = "recycle") {
        assert_eq!(a, b, "the cache hands back the block it was given last");
    }
    // SAFETY: as above.
    assert_eq!(unsafe { (*b).value }, 2);
    // SAFETY: as above.
    unsafe { drop_node(b) };
}

/// A value that counts its drops.
#[repr(C)]
struct Counted {
    retired: RetiredNode,
    drops: Arc<AtomicUsize>,
}

impl Drop for Counted {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn retire_node_drops_the_value_once_and_keeps_the_memory() {
    let drops = Arc::new(AtomicUsize::new(0));
    let slot = Atomic::new(alloc_node(Counted {
        retired: RetiredNode::new(),
        drops: drops.clone(),
    }));
    let mut retired = Vec::new();
    for _ in 0..1_000 {
        let guard = pin();
        let next = alloc_node(Counted {
            retired: RetiredNode::new(),
            drops: drops.clone(),
        });
        // SAFETY: a fresh node, published once.
        let old = slot.swap(unsafe { Shared::from_raw(next) }, Ordering::AcqRel, &guard);
        retired.push(old.as_raw() as usize);
        // SAFETY: unlinked by the swap, retired once.
        unsafe { retire_node(old.as_raw()) };
    }
    flush();
    flush();
    // Every retired value was dropped exactly once (a batch is freed once no
    // guard is pinned: none is here).
    assert_eq!(drops.load(Ordering::Relaxed), 1_000);
    // SAFETY: the slot's node is reached by no other thread.
    unsafe { drop_node(slot.load(Ordering::Acquire, &pin()).as_raw()) };
    assert_eq!(drops.load(Ordering::Relaxed), 1_001);
    if cfg!(feature = "recycle") {
        // The freed memory is in the cache: new nodes take it.
        let fresh: Vec<_> = (0..64).map(node).collect();
        let reused = fresh
            .iter()
            .filter(|&&p| retired.contains(&(p as usize)))
            .count();
        assert!(reused > 0, "no retired node's memory was reused");
        for p in fresh {
            // SAFETY: fresh nodes no other thread reaches.
            unsafe { drop_node(p) };
        }
    }
}

#[test]
fn free_node_frees_memory_whose_value_was_moved_out_or_never_written() {
    let drops = Arc::new(AtomicUsize::new(0));
    let p = alloc_node(Counted {
        retired: RetiredNode::new(),
        drops: drops.clone(),
    });
    // SAFETY: the value is moved out, then only the memory is freed.
    let value = unsafe { p.read() };
    // SAFETY: no value left to drop; nothing else reaches the node.
    unsafe { free_node(p) };
    drop(value);
    assert_eq!(drops.load(Ordering::Relaxed), 1);

    let uninit = alloc_node_uninit::<Node>();
    // SAFETY: never written, so only the memory is freed.
    unsafe { free_node(uninit.cast::<Node>()) };

    let written = alloc_node_uninit::<Node>();
    // SAFETY: the memory of a `Node`, written whole before it is dropped.
    unsafe {
        written.write(core::mem::MaybeUninit::new(Node {
            retired: RetiredNode::new(),
            value: 7,
        }))
    };
    // SAFETY: as above.
    unsafe { drop_node(written.cast::<Node>()) };
}

/// A node too large for every class.
#[repr(C)]
struct Big {
    retired: RetiredNode,
    bytes: [u8; 4096],
}

/// A node aligned to more than the cache's 16 bytes.
#[repr(C, align(64))]
struct Aligned {
    retired: RetiredNode,
    value: u64,
}

#[test]
fn nodes_outside_every_class_are_boxes() {
    let big = alloc_node(Big {
        retired: RetiredNode::new(),
        bytes: [3; 4096],
    });
    // SAFETY: a fresh node no other thread reaches.
    assert_eq!(unsafe { (*big).bytes[4095] }, 3);
    // SAFETY: as above.
    unsafe { drop_node(big) };
    for _ in 0..100 {
        let a = alloc_node(Aligned {
            retired: RetiredNode::new(),
            value: 9,
        });
        assert_eq!(
            a as usize % 64,
            0,
            "an over-aligned node lost its alignment"
        );
        // SAFETY: as above.
        unsafe { drop_node(a) };
    }
    let zst = alloc_node(());
    // SAFETY: a zero-sized node is a dangling, well-aligned pointer a Box frees.
    unsafe { drop_node(zst) };
}

// Under Miri, enough nodes for about sixty magazines to change threads
// through the depot, and a run that ends in minutes.
#[cfg(miri)]
const CROSSINGS: u64 = 2_000;
#[cfg(not(miri))]
const CROSSINGS: u64 = 100_000;

#[test]
fn nodes_cross_threads_and_their_values_arrive_whole() {
    use std::sync::mpsc;
    let (tx, rx) = mpsc::sync_channel::<usize>(256);
    let consumer = std::thread::spawn(move || {
        let mut sum = 0;
        for p in rx {
            let p = p as *mut Node;
            // SAFETY: the producer handed the node over and never touches it again.
            sum += unsafe { (*p).value };
            // SAFETY: as above.
            unsafe { drop_node(p) };
        }
        sum
    });
    let mut expected = 0;
    for i in 0..CROSSINGS {
        expected += i;
        tx.send(node(i) as usize).unwrap();
    }
    drop(tx);
    assert_eq!(consumer.join().unwrap(), expected);
}
