//! Every value a transaction stores is dropped exactly once: when it is
//! overwritten by a later commit (and kovan frees the node holding it), or
//! when its variable goes away, or when the transaction that would have
//! stored it rolls back.

use kovan::flush;
use kovan_stm::{Stm, StmError};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

/// Flushes until `drops` reaches `expected`: a value retired by a commit is freed once no
/// thread's reservation covers it, and the tests of this file run on parallel threads.
/// Fails with the count seen if it does not get there within ten seconds, or goes past it.
fn settle(drops: &AtomicUsize, expected: usize) {
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut backoff = Duration::from_micros(10);
    loop {
        flush();
        let seen = drops.load(Ordering::Relaxed);
        assert!(seen <= expected, "{seen} drops for {expected} values");
        if seen == expected {
            return;
        }
        assert!(
            Instant::now() < deadline,
            "{seen} of {expected} values dropped"
        );
        std::thread::sleep(backoff);
        backoff = (backoff * 2).min(Duration::from_millis(10));
    }
}

/// A value that counts its drops.
#[derive(Clone)]
struct Counted(Arc<AtomicUsize>);

impl Drop for Counted {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::Relaxed);
    }
}

#[test]
fn a_committed_value_is_dropped_once() {
    let drops = Arc::new(AtomicUsize::new(0));
    let stm = Stm::new();
    let var = stm.tvar(Counted(drops.clone()));
    for _ in 0..100 {
        stm.atomically(|tx| tx.store(&var, Counted(drops.clone())));
    }
    drop(var);
    // 1 initial value + 100 stored values, each dropped once.
    settle(&drops, 101);
}

#[test]
fn a_rolled_back_value_is_dropped_once() {
    let drops = Arc::new(AtomicUsize::new(0));
    let stm = Stm::new();
    let var = stm.tvar(Counted(drops.clone()));
    let mut first = true;
    let _: Result<(), StmError> = stm.atomically(|tx| {
        tx.store(&var, Counted(drops.clone()))?;
        if first {
            first = false;
            // Abort this attempt: its stored value must be dropped, once.
            return Err(StmError::Retry);
        }
        Ok(Ok(()))
    });
    drop(var);
    // The initial value, the rolled-back value, and the committed one.
    settle(&drops, 3);
}
