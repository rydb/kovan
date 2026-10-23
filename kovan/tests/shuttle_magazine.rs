//! Shuttle model-checked tests of the `recycle` feature's magazine cache: a
//! block is never in two hands at once, and none is lost, whatever order the
//! threads' trips to the depot take.
//!
//! Every node is tagged with its owner and a sequence number when it is
//! allocated, and checked when it is freed: if the cache handed one block to
//! two owners, the second owner's tag would overwrite the first's and the
//! first owner's check would fail. The producer allocates more nodes than its
//! two magazines hold, so the consumer, which frees them all, hands full
//! magazines to the depot, and the producer takes them back; both go through
//! the depot's two rings, the only shared state of the cache and its only
//! scheduling points.
//!
//! See `shuttle_reclaim.rs` for why the `shuttle` feature and per-task
//! thread-locals matter, and how to replay a failure.

#![cfg(all(feature = "shuttle", feature = "recycle"))]

use kovan::{RetiredNode, alloc_node, drop_node};
use shuttle::sync::mpsc;
use shuttle::thread;

/// More than one thread's two magazines hold (2 x 32 blocks).
const NODES: u64 = 100;

#[repr(C)]
struct Node {
    retired: RetiredNode,
    owner: u64,
    seq: u64,
}

struct Ptr(*mut Node);

// SAFETY: a node is handed whole from one thread to the next.
unsafe impl Send for Ptr {}

fn tagged(owner: u64, seq: u64) -> Ptr {
    Ptr(alloc_node(Node {
        retired: RetiredNode::new(),
        owner,
        seq,
    }))
}

/// Checks the node still holds its tag, then frees it.
fn check_and_free(p: Ptr, owner: u64, seq: u64) {
    // SAFETY: the caller owns the node.
    let node = unsafe { &*p.0 };
    assert_eq!(
        (node.owner, node.seq),
        (owner, seq),
        "a block was handed to two owners"
    );
    // SAFETY: as above; nothing reaches the node afterwards.
    unsafe { drop_node(p.0) };
}

/// A producer allocates, a consumer frees, and the producer allocates again
/// from what came back through the depot, while a third thread allocates and
/// frees on its own.
fn trade_through_the_depot() {
    let (tx, rx) = mpsc::channel::<(Ptr, u64)>();
    let producer = thread::spawn(move || {
        for seq in 0..NODES {
            tx.send((tagged(1, seq), seq)).unwrap();
        }
        // The consumer's magazines come back through the depot: take some.
        let again: Vec<_> = (0..NODES)
            .map(|seq| (tagged(1, 1_000 + seq), 1_000 + seq))
            .collect();
        thread::yield_now();
        for (p, seq) in again {
            check_and_free(p, 1, seq);
        }
    });
    let consumer = thread::spawn(move || {
        for (p, seq) in rx {
            check_and_free(p, 1, seq);
        }
    });
    let bystander = thread::spawn(|| {
        let mine: Vec<_> = (0..NODES).map(|seq| (tagged(3, seq), seq)).collect();
        thread::yield_now();
        for (p, seq) in mine {
            check_and_free(p, 3, seq);
        }
    });
    producer.join().unwrap();
    consumer.join().unwrap();
    bystander.join().unwrap();
}

#[test]
fn shuttle_magazines_trade_through_the_depot() {
    shuttle::check_pct(trade_through_the_depot, 2000, 3);
}

#[test]
fn shuttle_magazines_trade_through_the_depot_random() {
    shuttle::check_random(trade_through_the_depot, 2000);
}
