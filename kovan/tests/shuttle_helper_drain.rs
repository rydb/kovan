//! Shuttle model-checked test for the helper slots a transition drains: a list
//! a helper slot holds is taken once, while other threads keep retiring into
//! that slot and helping slow paths.
//!
//! A helper slot becomes active inside `help_thread`, and a retire that runs
//! while a help works can exchange a node into it. Every transition then takes
//! what such a slot holds with `detach_nodes`, racing an insert's exchange and
//! its link of the list it displaced. One reader pins and reads through its
//! guard twice with yield points between, and two writers publish twice each
//! and flush, retiring what every store replaced.
//!
//! The books are checked as well, as `shuttle_reclaim.rs` does: once the tasks
//! finish and every thread has flushed, every value created must have been
//! dropped exactly once. A list taken twice, or a node lost, shows up there.
//!
//! See `shuttle_reclaim.rs` for why the `shuttle` feature and the per-task
//! thread-local `Handle` matter, and how to replay a failure.

#![cfg(feature = "shuttle")]

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Clone)]
struct Counters {
    creates: Arc<AtomicUsize>,
    drops: Arc<AtomicUsize>,
}

impl Counters {
    fn new() -> Self {
        Self {
            creates: Arc::new(AtomicUsize::new(0)),
            drops: Arc::new(AtomicUsize::new(0)),
        }
    }
}

struct Counted {
    val: u64,
    counters: Counters,
}

impl Counted {
    fn new(val: u64, counters: &Counters) -> Self {
        counters.creates.fetch_add(1, Ordering::SeqCst);
        Self {
            val,
            counters: counters.clone(),
        }
    }
}

impl Drop for Counted {
    fn drop(&mut self) {
        self.counters.drops.fetch_add(1, Ordering::SeqCst);
    }
}

/// A reader holds a guard across two reads while two writers publish and
/// flush, so each store's retire races another thread's transition and helps.
fn helper_slot_drain_races_retires() {
    let counters = Counters::new();
    let atom = Arc::new(kovan::Atom::new(Counted::new(1, &counters)));

    let reader = {
        let atom = Arc::clone(&atom);
        shuttle::thread::spawn(move || {
            let guard = atom.load();
            let seen = guard.val;
            shuttle::thread::yield_now();
            assert!((1..=5).contains(&seen), "value corrupted: saw {seen}");
            drop(guard);
            // Drains this thread's own slot: a batch parked there waits for
            // the next pin otherwise.
            kovan::flush();
        })
    };

    let spawn_writer = {
        let atom = Arc::clone(&atom);
        let counters = counters.clone();
        move |base: u64| {
            let atom = Arc::clone(&atom);
            let counters = counters.clone();
            shuttle::thread::spawn(move || {
                drop(kovan::pin());
                for step in 0..2 {
                    atom.store(Counted::new(base + step, &counters));
                    kovan::flush();
                }
                // The slot stays deactivated after the last flush, so this one
                // takes what an insert slipped in under the previous one.
                kovan::flush();
            })
        }
    };
    let one = spawn_writer(2);
    let two = spawn_writer(4);

    reader.join().unwrap();
    one.join().unwrap();
    two.join().unwrap();
    // The closure above holds the last clone of the atom: without this the
    // drop below leaves it alive and the value it holds is never retired.
    drop(spawn_writer);
    drop(atom);

    // A handful of extra flushes drains any batch still parked in a slot.
    for _ in 0..8 {
        kovan::flush();
    }

    let created = counters.creates.load(Ordering::SeqCst);
    let dropped = counters.drops.load(Ordering::SeqCst);
    assert_eq!(
        created, dropped,
        "created {created}, dropped {dropped}: a helper slot's list was taken \
         twice or lost while a drain raced an insert"
    );
}

#[test]
fn shuttle_helper_slot_drain_races_retires() {
    shuttle::check_random(helper_slot_drain_races_retires, 20_000);
}
