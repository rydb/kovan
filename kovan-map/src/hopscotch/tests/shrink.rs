//! The shrink a remove asks for and the table's shrink word that decides it: a failed shrink is
//! not asked for again at the population it failed at, a clear and a publication forget it, and
//! the one compare a remove makes is exactly the quarter-full test with the threshold folded in.
//! Modelled in `proofs/tla/hopscotch/HopscotchMap.tla` and proved in
//! `proofs/lean/Kovan/HopscotchShrink.lean`.

use super::*;

/// `shrink_at` folds the quarter-full test into one count: a count below it is exactly the
/// two-part test it replaces, `4 * count < capacity` in a table larger than the least one, for
/// every capacity and count (the Rust side of `lt_shrinkAt_iff` in the Lean proof).
#[test]
fn shrink_at_is_exactly_the_quarter_full_test() {
    let quarter_full =
        |count: usize, capacity: usize| 4 * count < capacity && capacity > MIN_CAPACITY;
    for capacity in 0..=2_048usize {
        for count in 0..=capacity {
            assert_eq!(
                count < shrink_at(capacity),
                quarter_full(count, capacity),
                "{count} in {capacity}"
            );
        }
    }
    // Large capacities, at the edge of a quarter: `4 * count` stays in range below 2^62.
    for shift in 12..usize::BITS - 2 {
        let capacity = 1usize << shift;
        for count in [
            0,
            capacity / 4 - 1,
            capacity / 4,
            capacity / 4 + 1,
            capacity,
        ] {
            assert_eq!(
                count < shrink_at(capacity),
                quarter_full(count, capacity),
                "{count} in {capacity}"
            );
        }
    }
}

/// The current table's shrink word.
fn shrink_word(map: &HopscotchMap<u64, u64, Identity>) -> usize {
    let guard = pin();
    // SAFETY: the guard keeps the current table allocated while it is read.
    let table = unsafe { &*map.table.load(Ordering::Acquire, &guard).as_raw() };
    table.shrink_at.load(Ordering::Relaxed)
}

/// The table's shrink word through its life: a new table starts at its quarter, a failed shrink
/// lowers it to half the count it failed at, a clear sets it back, and a published table starts
/// at its own quarter, so a publication forgets every failed shrink of the table it replaced.
#[test]
fn the_shrink_word_follows_the_table() {
    let map = HopscotchMap::with_capacity_and_hasher(256, Identity);
    assert_eq!(shrink_word(&map), 64, "a new table starts at its quarter");
    // Two homes that fold into one cannot shrink: the remove of 40 that leaves 39 fails.
    for i in 0..20u64 {
        map.insert(i * 256, i);
        map.insert(i * 256 + 128, i);
    }
    map.remove(&0);
    assert_eq!(map.capacity(), 256, "the shrink did not fit");
    assert_eq!(shrink_word(&map), 19, "half of the 39 it failed at");
    map.clear();
    assert_eq!(shrink_word(&map), 64, "a clear sets the word back");
    // Refill past three quarters: the grow publishes a table of 512 with its own quarter.
    for i in 0..200u64 {
        map.insert(i, i);
    }
    assert_eq!(map.capacity(), 512, "grown once");
    assert_eq!(
        shrink_word(&map),
        128,
        "a published table starts at its own quarter"
    );
    // The least table never shrinks: its word is zero.
    let least = HopscotchMap::with_capacity_and_hasher(MIN_CAPACITY, Identity);
    assert_eq!(shrink_word(&least), 0);
}

/// Two homes that fold into one cannot shrink until their combined population
/// fits one neighborhood. Churn at the same population must not copy them again.
#[test]
fn a_failed_shrink_does_not_recopy_the_table_on_every_remove() {
    use alloc::sync::Arc;
    use core::sync::atomic::AtomicUsize;

    struct Counted(Arc<AtomicUsize>);
    impl Clone for Counted {
        fn clone(&self) -> Self {
            self.0.fetch_add(1, Ordering::Relaxed);
            Self(Arc::clone(&self.0))
        }
    }

    let clones = Arc::new(AtomicUsize::new(0));
    let map = HopscotchMap::with_capacity_and_hasher(256, Identity);
    for i in 0..20u64 {
        map.insert(i * 256, Counted(Arc::clone(&clones)));
        map.insert(i * 256 + 128, Counted(Arc::clone(&clones)));
    }
    map.remove(&0);
    assert_eq!(map.capacity(), 256);
    assert!(clones.load(Ordering::Relaxed) > 1, "first shrink attempted");
    clones.store(0, Ordering::Relaxed);
    for i in 20..28u64 {
        let key = i * 256;
        map.insert(key, Counted(Arc::clone(&clones)));
        map.remove(&key);
    }
    assert_eq!(
        clones.load(Ordering::Relaxed),
        8,
        "only removed values cloned"
    );
    for i in 1..20u64 {
        map.remove(&(i * 256));
    }
    map.remove(&128);
    map.remove(&(256 + 128));
    assert!(
        map.capacity() < 256,
        "a smaller population retries the shrink"
    );
    assert_eq!(map.len(), 18);
    for i in 2..20u64 {
        assert!(map.contains_key(&(i * 256 + 128)));
    }
}

/// A clear removes the entries a failed shrink recorded its threshold for, so
/// the next population shrinks as soon as it is underfull, not only once it
/// falls below half the old failed attempt.
#[test]
fn a_clear_forgets_a_failed_shrink() {
    let map = HopscotchMap::with_capacity_and_hasher(256, Identity);
    for i in 0..20u64 {
        map.insert(i * 256, i);
        map.insert(i * 256 + 128, i);
    }
    map.remove(&0);
    assert_eq!(
        map.capacity(),
        256,
        "two homes that fold into one cannot shrink"
    );
    map.clear();
    // One home of 30 entries: it fits a neighborhood at half the capacity.
    for i in 0..30u64 {
        map.insert(i * 256 + 1, i);
    }
    map.remove(&1);
    assert!(
        map.capacity() < 256,
        "an underfull population that fits shrinks after a clear"
    );
    assert_eq!(map.len(), 29);
    for i in 1..30u64 {
        assert!(map.contains_key(&(i * 256 + 1)));
    }
}
