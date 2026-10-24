//! The value `Atom::swap` and `AtomOption::take` hand back is the object the
//! readers that loaded it hold, not a copy: a value with interior mutability
//! is one object to all of them, and it is dropped once, after they are gone.

use kovan::{Atom, AtomOption};
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering::SeqCst};
use std::sync::{Arc, Barrier, Mutex, TryLockError, mpsc};
use std::thread;
use std::time::{Duration, Instant};

#[test]
fn swap_hands_back_the_object_a_reader_holds() {
    let atom = Atom::new(AtomicU64::new(0));
    let reader = atom.load();
    let removed = atom.swap(AtomicU64::new(9));
    assert!(std::ptr::eq(&*removed, &*reader));
    removed.fetch_add(1, SeqCst);
    assert_eq!(reader.load(SeqCst), 1, "a copy would not see the add");
    assert_eq!(atom.load().load(SeqCst), 9);
}

#[test]
fn a_removed_mutex_is_the_one_a_reader_locked() {
    let atom = Atom::new(Mutex::new(vec![1u8]));
    let reader = atom.load();
    let held = reader.lock().unwrap();
    let removed = atom.swap(Mutex::new(Vec::new()));
    assert!(
        matches!(removed.try_lock(), Err(TryLockError::WouldBlock)),
        "the reader's lock must hold the removed value's mutex too"
    );
    drop(held);
    removed.lock().unwrap().push(2);
    assert_eq!(*reader.lock().unwrap(), [1, 2]);
}

#[test]
fn take_hands_back_the_object_a_reader_holds() {
    let atom = AtomOption::some(AtomicU64::new(5));
    let reader = atom.load().unwrap();
    let removed = atom.take().unwrap();
    assert!(std::ptr::eq(&*removed, &*reader));
    removed.store(6, SeqCst);
    assert_eq!(reader.load(SeqCst), 6);
    assert!(atom.take().is_none());
}

/// A value that counts its drops.
struct Counted(Arc<AtomicUsize>);

impl Drop for Counted {
    fn drop(&mut self) {
        self.0.fetch_add(1, SeqCst);
    }
}

/// Flushes until `n` values are dropped, as other tests' pins may hold the
/// frees back for a while, and fails at a deadline; then checks that no more
/// than `n` were.
fn wait_for_drops(drops: &AtomicUsize, n: usize) {
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut pause = Duration::from_micros(50);
    while drops.load(SeqCst) < n {
        assert!(
            Instant::now() < deadline,
            "only {} of {n} values dropped",
            drops.load(SeqCst)
        );
        kovan::flush();
        thread::sleep(pause);
        pause = (pause * 2).min(Duration::from_millis(20));
    }
    assert_eq!(drops.load(SeqCst), n, "a value dropped twice");
}

#[test]
fn a_removed_value_is_dropped_once() {
    let drops = Arc::new(AtomicUsize::new(0));
    let atom = Atom::new(Counted(drops.clone()));
    drop(atom.swap(Counted(drops.clone())));
    let opt = AtomOption::some(Counted(drops.clone()));
    drop(opt.take());
    wait_for_drops(&drops, 2);
    drop(atom);
    drop(opt);
    assert_eq!(
        drops.load(SeqCst),
        3,
        "and the stored one at the Atom's drop"
    );
}

#[test]
fn into_inner_unchecked_moves_the_value_out_once() {
    let drops = Arc::new(AtomicUsize::new(0));
    let atom = Atom::new(Counted(drops.clone()));
    let removed = atom.swap(Counted(drops.clone()));
    // SAFETY: no reader loaded the old value.
    let value = unsafe { removed.into_inner_unchecked() };
    assert_eq!(drops.load(SeqCst), 0);
    drop(value);
    kovan::flush();
    assert_eq!(
        drops.load(SeqCst),
        1,
        "moved out, so dropped by its owner only"
    );
    drop(atom);
    assert_eq!(drops.load(SeqCst), 2);
}

#[test]
fn a_reader_on_another_thread_keeps_the_value_past_the_removed_drop() {
    let atom = Arc::new(Atom::new(String::from("first value, on the heap")));
    let loaded = Arc::new(Barrier::new(2));
    let (done_tx, done_rx) = mpsc::channel::<()>();
    let reader = {
        let (atom, loaded) = (atom.clone(), loaded.clone());
        thread::spawn(move || {
            let guard = atom.load();
            loaded.wait();
            // Wait until the writer dropped the `Removed` and flushed.
            done_rx.recv().unwrap();
            guard.clone()
        })
    };
    loaded.wait();
    let removed = atom.swap(String::from("second"));
    assert_eq!(*removed, "first value, on the heap");
    drop(removed);
    for _ in 0..4 {
        kovan::flush();
    }
    done_tx.send(()).unwrap();
    assert_eq!(reader.join().unwrap(), "first value, on the heap");
    assert_eq!(*atom.load(), "second");
}
