//! `SegQueue` order, delivery, `try_pop`, `len` and drop accounting, on real
//! threads.
//!
//! Every pushed value is `producer << 32 | sequence`, so a consumer can tell
//! whose value it got and where in that producer's sequence it was.

use kovan_queue::seg_queue::{SegQueue, TryPopError};
use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Barrier, Mutex};
use std::thread;

/// Cells per segment in `seg_queue.rs` (private there).
const SEGMENT_SIZE: u64 = 32;

fn tag(producer: u64, seq: u64) -> u64 {
    (producer << 32) | seq
}

fn producer_of(v: u64) -> u64 {
    v >> 32
}

fn seq_of(v: u64) -> u64 {
    v & 0xffff_ffff
}

/// Producers each push `per` increasing values; the consumers pop until all
/// are out. Returns what each consumer popped, in its order.
fn run(producers: u64, consumers: usize, per: u64, use_try_pop: bool) -> Vec<Vec<u64>> {
    let q = Arc::new(SegQueue::new());
    let start = Arc::new(Barrier::new(producers as usize + consumers));
    let left = Arc::new(AtomicUsize::new((producers * per) as usize));
    let mut handles = Vec::new();
    for p in 0..producers {
        let (q, start) = (Arc::clone(&q), Arc::clone(&start));
        handles.push(thread::spawn(move || {
            start.wait();
            for s in 0..per {
                q.push(tag(p, s));
            }
            Vec::new()
        }));
    }
    for _ in 0..consumers {
        let (q, start, left) = (Arc::clone(&q), Arc::clone(&start), Arc::clone(&left));
        handles.push(thread::spawn(move || {
            start.wait();
            let mut got = Vec::new();
            while left.load(Ordering::Relaxed) > 0 {
                let v = if use_try_pop {
                    q.try_pop().ok()
                } else {
                    q.pop()
                };
                match v {
                    Some(v) => {
                        got.push(v);
                        left.fetch_sub(1, Ordering::Relaxed);
                    }
                    None => std::hint::spin_loop(),
                }
            }
            got
        }));
    }
    let out: Vec<Vec<u64>> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    assert_eq!(q.pop(), None, "a value was left behind");
    assert!(q.is_empty());
    assert_eq!(q.len(), 0);
    out.into_iter().filter(|v| !v.is_empty()).collect()
}

/// Every value came out exactly once.
fn check_exactly_once(out: &[Vec<u64>], producers: u64, per: u64) {
    let mut seen = HashSet::new();
    for v in out.iter().flatten() {
        assert!(seen.insert(*v), "value {v:#x} popped twice");
    }
    assert_eq!(seen.len() as u64, producers * per, "values were lost");
}

/// Each consumer saw each producer's values in increasing order (true for
/// any number of consumers: a consumer's pops are sequential).
fn check_per_producer_order(out: &[Vec<u64>], producers: u64) {
    for got in out {
        let mut last = vec![None; producers as usize];
        for &v in got {
            let p = producer_of(v) as usize;
            if let Some(prev) = last[p] {
                assert!(seq_of(v) > prev, "producer {p}: {} after {prev}", seq_of(v));
            }
            last[p] = Some(seq_of(v));
        }
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn single_consumer_sees_every_producer_in_order() {
    for producers in [1, 2, 4, 8] {
        let per = 20_000;
        let out = run(producers, 1, per, false);
        check_exactly_once(&out, producers, per);
        check_per_producer_order(&out, producers);
        // One consumer: each producer's values are contiguous in sequence.
        let mut next = vec![0; producers as usize];
        for &v in &out[0] {
            let p = producer_of(v) as usize;
            assert_eq!(
                seq_of(v),
                next[p],
                "producer {p} skipped or repeated a value"
            );
            next[p] += 1;
        }
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn single_consumer_try_pop_sees_every_producer_in_order() {
    let (producers, per) = (4, 20_000);
    let out = run(producers, 1, per, true);
    check_exactly_once(&out, producers, per);
    check_per_producer_order(&out, producers);
}

#[test]
#[cfg_attr(miri, ignore)]
fn many_consumers_get_every_value_once_and_in_order() {
    for (producers, consumers) in [(2, 2), (4, 4), (8, 3), (3, 8)] {
        let per = 10_000;
        let out = run(producers, consumers, per, false);
        check_exactly_once(&out, producers, per);
        check_per_producer_order(&out, producers);
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn mixed_pop_and_try_pop_consumers() {
    let (producers, per) = (4u64, 10_000u64);
    let q = Arc::new(SegQueue::new());
    let left = Arc::new(AtomicUsize::new((producers * per) as usize));
    let mut handles = Vec::new();
    for p in 0..producers {
        let q = Arc::clone(&q);
        handles.push(thread::spawn(move || {
            for s in 0..per {
                q.push(tag(p, s));
            }
            Vec::new()
        }));
    }
    for c in 0..4 {
        let (q, left) = (Arc::clone(&q), Arc::clone(&left));
        handles.push(thread::spawn(move || {
            let mut got = Vec::new();
            while left.load(Ordering::Relaxed) > 0 {
                let v = if c % 2 == 0 {
                    q.pop()
                } else {
                    q.try_pop().ok()
                };
                if let Some(v) = v {
                    got.push(v);
                    left.fetch_sub(1, Ordering::Relaxed);
                }
            }
            got
        }));
    }
    let out: Vec<Vec<u64>> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    check_exactly_once(&out, producers, per);
    check_per_producer_order(&out, producers);
}

/// Real-time order across producers: a value pushed after another value's
/// push returned (observed through a flag) never comes out before it.
#[test]
#[cfg_attr(miri, ignore)]
fn a_completed_push_comes_out_before_a_later_one() {
    for _ in 0..200 {
        let q = Arc::new(SegQueue::new());
        let first_done = Arc::new(AtomicBool::new(false));
        let a = {
            let (q, first_done) = (Arc::clone(&q), Arc::clone(&first_done));
            thread::spawn(move || {
                q.push(1u64);
                first_done.store(true, Ordering::SeqCst);
            })
        };
        let b = {
            let (q, first_done) = (Arc::clone(&q), Arc::clone(&first_done));
            thread::spawn(move || {
                while !first_done.load(Ordering::SeqCst) {
                    std::hint::spin_loop();
                }
                q.push(2u64);
            })
        };
        let c = {
            let q = Arc::clone(&q);
            thread::spawn(move || {
                let mut got = Vec::new();
                while got.len() < 2 {
                    if let Some(v) = q.pop() {
                        got.push(v);
                    }
                }
                got
            })
        };
        a.join().unwrap();
        b.join().unwrap();
        assert_eq!(c.join().unwrap(), vec![1, 2]);
    }
}

/// Linearizability of small concurrent histories: every completed pop's
/// value was pushed, and an empty answer is impossible while a value whose
/// push returned before the pop started is still in the queue and no other
/// pop is running.
#[test]
#[cfg_attr(miri, ignore)]
fn pop_after_completed_push_never_answers_empty() {
    for round in 0..2_000u64 {
        let q = SegQueue::new();
        // Fill to just below, at and past a segment boundary.
        let n = round % (2 * SEGMENT_SIZE + 2);
        for i in 0..n {
            q.push(i);
        }
        for i in 0..n {
            assert_eq!(q.pop(), Some(i));
        }
        let q = Arc::new(q);
        let pusher = {
            let q = Arc::clone(&q);
            thread::spawn(move || q.push(u64::MAX))
        };
        pusher.join().unwrap();
        assert_eq!(q.pop(), Some(u64::MAX), "round {round}");
        assert_eq!(q.pop(), None);
    }
}

#[test]
fn try_pop_tells_empty_from_value() {
    let q = SegQueue::new();
    assert_eq!(q.try_pop(), Err(TryPopError::Empty));
    for i in 0..3 * SEGMENT_SIZE {
        q.push(i);
    }
    for i in 0..3 * SEGMENT_SIZE {
        assert_eq!(q.try_pop(), Ok(i));
    }
    assert_eq!(q.try_pop(), Err(TryPopError::Empty));
    assert_eq!(q.pop(), None);
    assert_eq!(TryPopError::Empty.to_string(), "the queue is empty");
    assert_eq!(
        TryPopError::Busy.to_string(),
        "the next value is still being pushed"
    );
}

/// `Busy` only while a push is in progress: once the only producer's push
/// has returned (seen through a flag read before the call), `try_pop`
/// answers the value or `Empty`, never `Busy`.
#[test]
#[cfg_attr(miri, ignore)]
fn no_busy_once_the_push_returned() {
    for round in 0..2_000u64 {
        let q = Arc::new(SegQueue::new());
        let done = Arc::new(AtomicBool::new(false));
        let producer = {
            let (q, done) = (Arc::clone(&q), Arc::clone(&done));
            thread::spawn(move || {
                q.push(round);
                done.store(true, Ordering::SeqCst);
            })
        };
        loop {
            let pushed = done.load(Ordering::SeqCst);
            match q.try_pop() {
                Ok(v) => {
                    assert_eq!(v, round);
                    break;
                }
                Err(TryPopError::Busy) => assert!(!pushed, "Busy after the push returned"),
                Err(TryPopError::Empty) => assert!(!pushed, "Empty after the push returned"),
            }
        }
        producer.join().unwrap();
        assert_eq!(q.try_pop(), Err(TryPopError::Empty));
    }
}

#[test]
fn len_and_is_empty_at_rest() {
    let q = SegQueue::new();
    assert_eq!(q.len(), 0);
    assert!(q.is_empty());
    for i in 0..5 * SEGMENT_SIZE + 3 {
        q.push(i);
        assert_eq!(q.len() as u64, i + 1);
        assert!(!q.is_empty());
    }
    for i in 0..5 * SEGMENT_SIZE + 3 {
        assert_eq!(q.pop(), Some(i));
        assert_eq!(q.len() as u64, 5 * SEGMENT_SIZE + 2 - i);
    }
    assert!(q.is_empty());
    // Exactly one segment's worth, so the head segment ends drained with no
    // successor.
    for i in 0..SEGMENT_SIZE {
        q.push(i);
    }
    for _ in 0..SEGMENT_SIZE {
        q.pop();
    }
    assert!(q.is_empty());
    assert_eq!(q.len(), 0);
    assert_eq!(q.pop(), None);
    assert_eq!(q.try_pop(), Err(TryPopError::Empty));
    q.push(7);
    assert_eq!(q.len(), 1);
    assert!(!q.is_empty());
    assert_eq!(q.pop(), Some(7));
}

/// A value that counts its drops.
struct Counted {
    id: u64,
    drops: Arc<Mutex<Vec<u64>>>,
}

impl Drop for Counted {
    fn drop(&mut self) {
        self.drops.lock().unwrap().push(self.id);
    }
}

#[test]
fn drop_drops_every_remaining_value_once() {
    for (pushed, popped) in [
        (0, 0),
        (1, 0),
        (1, 1),
        (31, 5),
        (32, 32),
        (33, 32),
        (100, 37),
        (200, 0),
    ] {
        let drops = Arc::new(Mutex::new(Vec::new()));
        {
            let q = SegQueue::new();
            for id in 0..pushed {
                q.push(Counted {
                    id,
                    drops: Arc::clone(&drops),
                });
            }
            for id in 0..popped {
                let v = q.pop().unwrap();
                assert_eq!(v.id, id);
            }
        }
        kovan::flush();
        let mut d = drops.lock().unwrap().clone();
        d.sort_unstable();
        assert_eq!(
            d,
            (0..pushed).collect::<Vec<_>>(),
            "pushed {pushed}, popped {popped}"
        );
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn drop_after_concurrent_use_drops_the_rest_once() {
    let drops = Arc::new(Mutex::new(Vec::new()));
    let total = 4 * 5_000u64;
    let popped = Arc::new(AtomicUsize::new(0));
    {
        let q = Arc::new(SegQueue::new());
        let mut handles = Vec::new();
        for p in 0..4u64 {
            let (q, drops) = (Arc::clone(&q), Arc::clone(&drops));
            handles.push(thread::spawn(move || {
                for s in 0..5_000 {
                    q.push(Counted {
                        id: tag(p, s),
                        drops: Arc::clone(&drops),
                    });
                }
            }));
        }
        for _ in 0..3 {
            let (q, popped) = (Arc::clone(&q), Arc::clone(&popped));
            handles.push(thread::spawn(move || {
                for _ in 0..3_000 {
                    if q.pop().is_some() {
                        popped.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }));
        }
        for h in handles {
            h.join().unwrap();
        }
    }
    kovan::flush();
    let d = drops.lock().unwrap();
    let unique: HashSet<u64> = d.iter().copied().collect();
    assert_eq!(unique.len(), d.len(), "a value was dropped twice");
    assert_eq!(d.len() as u64, total, "a value was never dropped");
}

/// No `T: 'static`: a queue of borrowed values.
#[test]
fn holds_borrowed_values() {
    let words = [String::from("a"), String::from("b"), String::from("c")];
    let q: SegQueue<&str> = SegQueue::new();
    for _ in 0..40 {
        for w in &words {
            q.push(w.as_str());
        }
    }
    for _ in 0..40 {
        for w in &words {
            assert_eq!(q.pop(), Some(w.as_str()));
        }
    }
    let local = 5u64;
    let r = &local;
    let q2 = SegQueue::new();
    for _ in 0..100 {
        q2.push(r);
    }
    drop(q2);
}

#[test]
fn zero_sized_values() {
    let q = SegQueue::new();
    for _ in 0..1000 {
        q.push(());
    }
    assert_eq!(q.len(), 1000);
    for _ in 0..1000 {
        assert_eq!(q.pop(), Some(()));
    }
    assert_eq!(q.pop(), None);
}

#[test]
fn queue_is_send_and_sync() {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<SegQueue<u64>>();
    assert_send_sync::<SegQueue<String>>();
    assert_send_sync::<SegQueue<&'static str>>();
}
