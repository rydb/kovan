//! The interleavings a displacement turns on: a lookup, a claim, a remove and a walk racing the
//! move of an entry, each stopped step by step through `pause`, and the walks and folds that meet
//! a key a displacement moved ahead of them exactly once.

use super::*;

/// A lookup that read its home's hop bits before a displacement moved its key, and scans after
/// the move, finds the key's old slot taken by another key. The move stamp it then re-reads has
/// advanced, so it scans again and finds the key in its new slot. Before the fix it answered
/// `None` for a key present throughout.
#[test]
fn a_lookup_that_read_the_hop_bits_before_a_move_finds_the_moved_key() {
    let map = displacing_layout();
    let (reader, arrival, release) = {
        let map = Arc::clone(&map);
        stopped_at(Point::LookupReadHops, move || map.get(&2))
    };
    arrival
        .recv_timeout(MEET)
        .expect("the lookup read key 2's hop bits");
    assert_eq!(map.insert(64, 64), None);
    assert_displaced(&map);
    release.send(()).expect("let the lookup scan");
    assert_eq!(reader.join().expect("the lookup"), Some(2));
}

/// Stopped at each step of a move (the entry linked in both slots; then unlinked from its old
/// slot, whose hop bit is still set), a lookup finds the entry and a walk yields every key once.
#[test]
fn a_move_keeps_its_entry_visible_to_lookups_and_walks_at_every_step() {
    for point in [Point::MoveLinkedTwice, Point::MoveUnlinked] {
        let map = displacing_layout();
        let (mover, arrival, release) = {
            let map = Arc::clone(&map);
            stopped_at(point, move || map.insert(64, 64))
        };
        arrival.recv_timeout(MEET).expect("the insert moves key 2");
        let in_old_slot = (point == Point::MoveLinkedTwice).then_some(2);
        assert_eq!(key_at(&map, 2), in_old_slot, "{point:?}");
        assert_eq!(key_at(&map, 33), Some(2), "{point:?}");
        assert_eq!(map.get(&2), Some(2), "{point:?}: a lookup missed the key");
        assert_eq!(walked_keys(&map), keys_and(&[]), "{point:?}: a walk");
        release.send(()).expect("let the move finish");
        assert_eq!(mover.join().expect("the insert"), None);
        assert_displaced(&map);
        assert_eq!(map.get(&2), Some(2));
        assert_eq!(walked_keys(&map), keys_and(&[64]));
    }
}

/// A test that gives up on a thread it paused inside a move (it drops the channel that would
/// release it) leaves the map whole: the thread finishes the move, so no entry stays linked in
/// two slots and dropping the map frees every entry once.
#[test]
fn an_abandoned_pause_inside_a_move_leaves_the_map_whole() {
    for point in [Point::MoveLinkedTwice, Point::MoveUnlinked] {
        let map = displacing_layout();
        let (mover, mover_arrival, mover_release) = {
            let map = Arc::clone(&map);
            stopped_at(point, move || map.insert(64, 64))
        };
        mover_arrival
            .recv_timeout(MEET)
            .expect("the insert moves key 2");
        drop(mover_release);
        assert_eq!(
            mover.join().expect("the insert finishes"),
            None,
            "{point:?}"
        );
        assert_eq!(map.get(&2), Some(2), "{point:?}");
        assert_eq!(map.get(&64), Some(64), "{point:?}");
        assert_eq!(map.len(), 34, "{point:?}");
        assert_eq!(walked_keys(&map), keys_and(&[64]), "{point:?}");
        drop(map);
    }
}

/// A claim of a key whose entry a displacement is moving finds the key, at either point of the
/// move, without waiting for the move's home guard: its lookup rescans when the move stamp
/// changed. Before the fix the claim scanned mid-move, missed the entry and linked a second one.
#[test]
fn a_claim_of_a_key_being_moved_finds_it() {
    for point in [Point::MoveLinkedTwice, Point::MoveUnlinked] {
        let map = displacing_layout();
        let (mover, mover_arrival, mover_release) = {
            let map = Arc::clone(&map);
            stopped_at(point, move || map.insert(64, 64))
        };
        mover_arrival
            .recv_timeout(MEET)
            .expect("the insert moves key 2");
        // Mid-move, with the move holding key 2's home guard: both claims find key 2 by the
        // lookup `get` makes and answer without waiting for the guard.
        assert_eq!(map.insert_if_absent(2, 99), Some(2), "{point:?}");
        assert_eq!(map.get_or_insert(2, 98), 2, "{point:?}");
        mover_release.send(()).expect("let the move finish");
        assert_eq!(mover.join().expect("the insert"), None);
        assert_eq!(map.get(&2), Some(2));
        assert_eq!(map.len(), 34);
        assert_eq!(walked_keys(&map), keys_and(&[64]));
    }
}

/// Two claims of a key whose insert has to displace an entry have one winner: the second waits
/// for the first, which holds the key's home guard through the whole move.
#[test]
fn two_claims_of_a_key_that_needs_a_displacement_have_one_winner() {
    let map = displacing_layout();
    let (first, first_arrival, first_release) = {
        let map = Arc::clone(&map);
        stopped_at(Point::MoveLinkedTwice, move || map.insert_if_absent(64, 1))
    };
    first_arrival
        .recv_timeout(MEET)
        .expect("the first claim moves key 2");
    let (second, second_arrival, second_release) = {
        let map = Arc::clone(&map);
        stopped_at(Point::WriterMetHeldGuard, move || {
            map.insert_if_absent(64, 2)
        })
    };
    second_arrival
        .recv_timeout(MEET)
        .expect("the second claim waits for bucket 0's guard");
    first_release.send(()).expect("let the first claim finish");
    assert_eq!(first.join().expect("the first claim"), None);
    second_release.send(()).expect("let the second claim run");
    assert_eq!(second.join().expect("the second claim"), Some(1));
    assert_displaced(&map);
    assert_eq!(map.get(&64), Some(1));
    assert_eq!(map.len(), 34);
    assert_eq!(walked_keys(&map), keys_and(&[64]));
}

/// A remove of a key whose entry a displacement is moving waits for the move and removes the
/// key. Before the fix the remove could find the entry mid-move, lose its unlink to the move and
/// answer `None` for a present key.
#[test]
fn a_remove_racing_the_move_of_its_key_removes_it() {
    for point in [Point::MoveLinkedTwice, Point::MoveUnlinked] {
        let map = displacing_layout();
        let (mover, mover_arrival, mover_release) = {
            let map = Arc::clone(&map);
            stopped_at(point, move || map.insert(64, 64))
        };
        mover_arrival
            .recv_timeout(MEET)
            .expect("the insert moves key 2");
        let (remover, remover_arrival, remover_release) = {
            let map = Arc::clone(&map);
            stopped_at(Point::WriterMetHeldGuard, move || map.remove(&2))
        };
        remover_arrival
            .recv_timeout(MEET)
            .expect("the remove waits for the move");
        mover_release.send(()).expect("let the move finish");
        assert_eq!(mover.join().expect("the insert"), None);
        remover_release.send(()).expect("let the remove go on");
        assert_eq!(remover.join().expect("the remove"), Some(2), "{point:?}");
        assert_eq!(map.get(&2), None);
        assert_eq!(map.len(), 33);
        let want: Vec<u64> = (0..=32).filter(|k| *k != 2).chain([64]).collect();
        assert_eq!(walked_keys(&map), want);
    }
}

/// A walk that met key 2 in slot 2 before a displacement moved it to slot 33, ahead of the walk,
/// does not yield it again there: the move links the same entry, which the walk recognizes.
/// Before the fix the move linked a copy and the walk yielded key 2 twice.
#[test]
fn a_walk_meets_a_key_a_displacement_moved_ahead_of_it_once() {
    let map = displacing_layout();
    let mut walk = map.iter();
    let mut seen: Vec<u64> = walk.by_ref().take(3).map(|(k, _)| k).collect();
    assert_eq!(seen, [0, 1, 2]);
    assert_eq!(map.insert(64, 64), None);
    assert_displaced(&map);
    seen.extend(walk.map(|(k, _)| k));
    seen.sort_unstable();
    assert_eq!(seen, keys_and(&[]), "key 2 once: not met again in slot 33");
}

/// A walk meets a key once even when a displacement moves it ahead of the walk and an update
/// then replaces its entry there with a new one: the walk recognizes the key.
#[test]
fn a_walk_meets_a_key_once_when_it_is_moved_ahead_and_updated() {
    let map = displacing_layout();
    let mut walk = map.iter();
    let mut seen: Vec<(u64, u64)> = walk.by_ref().take(3).collect();
    assert_eq!(seen, [(0, 0), (1, 1), (2, 2)]);
    assert_eq!(map.insert(64, 64), None);
    assert_displaced(&map);
    assert_eq!(map.insert(2, 200), Some(2), "key 2 is replaced in slot 33");
    seen.extend(walk);
    seen.sort_unstable();
    let want: Vec<(u64, u64)> = (0..=32).map(|k| (k, k)).collect();
    assert_eq!(seen, want, "key 2 once, as the walk first met it");
}

/// A walk that met key 2 in slot 2 through `next`, and folds the rest after a displacement moved
/// key 2 to slot 33, does not count it again there: the fold recognizes what `next` met.
#[test]
fn a_fold_after_next_meets_a_key_a_displacement_moved_ahead_of_it_once() {
    let map = displacing_layout();
    let mut walk = map.iter();
    let seen: Vec<u64> = walk.by_ref().take(3).map(|(k, _)| k).collect();
    assert_eq!(seen, [0, 1, 2]);
    assert_eq!(map.insert(64, 64), None);
    assert_displaced(&map);
    // Keys 3..=32 in slots 3..=32, and key 2 in slot 33 once more.
    assert_eq!(walk.count(), 30, "key 2 once: not met again in slot 33");
}

/// A 64-bucket map whose keys `32..64` sit each in its home slot (under `Identity` or `Tagged`),
/// so the neighborhood of bucket 32 (slots 32..64) is full and slots 64.. are free.
fn upper_half_layout<S: BuildHasher + Default>() -> HopscotchMap<u64, u64, S> {
    let map = HopscotchMap::with_capacity_and_hasher(64, S::default());
    for k in 32..64 {
        map.insert(k, k);
    }
    map
}

/// How many times each key comes out of a fold over `map` whose closure runs `write` once, at
/// the first entry it gets.
fn fold_counts<S: BuildHasher>(
    map: &HopscotchMap<u64, u64, S>,
    write: impl FnOnce(),
) -> std::collections::BTreeMap<u64, usize> {
    let mut write = Some(write);
    map.iter()
        .fold(std::collections::BTreeMap::new(), |mut counts, (k, _)| {
            if let Some(write) = write.take() {
                write();
            }
            *counts.entry(k).or_insert(0) += 1;
            counts
        })
}

/// A fold meets a key once when a displacement, made from the fold's own closure, moves the key
/// from a slot the fold may already have read to one it reads later: inserting key 96 (home
/// bucket 32) moves key 33 from slot 33 to slot 64, the first slot of the table's second group
/// of `u64::BITS` slots, which the fold reads after it yields the first.
fn a_fold_meets_a_key_a_displacement_moved_ahead_of_it_once<S: BuildHasher + Default>() {
    let map = upper_half_layout::<S>();
    let counts = fold_counts(&map, || {
        assert_eq!(map.insert(96, 96), None);
        assert_eq!(
            key_at(&map, 33),
            Some(96),
            "key 96 took the slot key 33 left"
        );
        assert_eq!(key_at(&map, 64), Some(33), "key 33 moved to slot 64");
    });
    for k in 32..64 {
        assert_eq!(
            counts.get(&k),
            Some(&1),
            "key {k}, present throughout, once"
        );
    }
    assert!(counts.values().all(|&n| n == 1), "no key twice: {counts:?}");
}

#[test]
fn a_fold_meets_a_key_a_displacement_moved_ahead_of_it_once_identity() {
    a_fold_meets_a_key_a_displacement_moved_ahead_of_it_once::<Identity>();
}

#[test]
fn a_fold_meets_a_key_a_displacement_moved_ahead_of_it_once_tagged() {
    a_fold_meets_a_key_a_displacement_moved_ahead_of_it_once::<Tagged>();
}

/// A fold meets a key once when the fold's own closure removes it from a slot the fold may
/// already have read and inserts it again into one the fold reads later: key 127 (home bucket
/// 63) takes slot 63 first, so key 63 lands in slot 64. The new entry is another allocation of
/// the same key, which the fold recognizes by comparing keys.
fn a_fold_meets_a_key_reinserted_ahead_of_it_once<S: BuildHasher + Default>() {
    let map = upper_half_layout::<S>();
    let counts = fold_counts(&map, || {
        assert_eq!(map.remove(&63), Some(63));
        assert_eq!(map.insert(127, 127), None);
        assert_eq!(map.insert(63, 630), None);
        assert_eq!(key_at(&map, 63), Some(127));
        assert_eq!(key_at(&map, 64), Some(63), "key 63 again, in slot 64");
    });
    for k in 32..64 {
        assert_eq!(counts.get(&k), Some(&1), "key {k} once");
    }
    assert!(counts.values().all(|&n| n == 1), "no key twice: {counts:?}");
}

#[test]
fn a_fold_meets_a_key_reinserted_ahead_of_it_once_identity() {
    a_fold_meets_a_key_reinserted_ahead_of_it_once::<Identity>();
}

#[test]
fn a_fold_meets_a_key_reinserted_ahead_of_it_once_tagged() {
    a_fold_meets_a_key_reinserted_ahead_of_it_once::<Tagged>();
}

std::thread_local! {
    /// The clones of [`Clones`] values made on this thread.
    static CLONED: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
}

/// A key or value that counts its clones on the thread that makes them.
#[derive(PartialEq, Eq, Hash)]
struct Clones(u64);

impl Clone for Clones {
    fn clone(&self) -> Self {
        CLONED.with(|cloned| cloned.set(cloned.get() + 1));
        Self(self.0)
    }
}

/// The clones of [`Clones`] values `walk` makes.
fn clones_in(walk: impl FnOnce()) -> usize {
    let before = CLONED.with(core::cell::Cell::get);
    walk();
    CLONED.with(core::cell::Cell::get) - before
}

/// A walk of the keys clones no value and a walk of the values no key, through `next` and
/// through `fold` alike; a walk of the entries clones both.
#[test]
fn keys_and_values_clone_only_what_they_yield() {
    let by_key = HopscotchMap::<Clones, u64>::new();
    let by_value = HopscotchMap::<u64, Clones>::new();
    for k in 0..100 {
        by_key.insert(Clones(k), k);
        by_value.insert(k, Clones(k));
    }
    assert_eq!(clones_in(|| assert_eq!(by_value.keys().count(), 100)), 0);
    assert_eq!(
        clones_in(|| assert_eq!(by_value.keys().collect::<Vec<_>>().len(), 100)),
        0
    );
    assert_eq!(clones_in(|| assert_eq!(by_key.values().count(), 100)), 0);
    assert_eq!(
        clones_in(|| assert_eq!(by_key.values().collect::<Vec<_>>().len(), 100)),
        0
    );
    assert_eq!(clones_in(|| assert_eq!(by_key.keys().count(), 100)), 100);
    assert_eq!(clones_in(|| assert_eq!(by_value.iter().count(), 100)), 100);
}

/// A displacement whose first candidate's home guard is held by another writer moves the next
/// candidate instead of growing the table, and never waits for the held guard. Key 66's home is
/// bucket 2, key 2's home.
#[test]
fn a_displacement_moves_another_entry_when_one_home_is_held() {
    let map = displacing_layout();
    let (holder, holder_arrival, holder_release) = {
        let map = Arc::clone(&map);
        stopped_at(Point::InGuardBeforeClaim, move || {
            map.insert_if_absent(66, 66)
        })
    };
    holder_arrival
        .recv_timeout(MEET)
        .expect("the insert of key 66 holds bucket 2's guard");
    // Key 2 cannot move while its home is held, so key 3 moves from slot 3 to slot 33.
    assert_eq!(map.insert(64, 64), None);
    assert_eq!(key_at(&map, 3), Some(64));
    assert_eq!(key_at(&map, 33), Some(3));
    assert_eq!(map.capacity(), 64, "a held home is not a full table");
    holder_release.send(()).expect("let key 66 claim a slot");
    assert_eq!(holder.join().expect("the insert of key 66"), None);
    // Key 66's neighborhood (slots 2..34) is full now, so its insert moves key 4 to slot 34.
    assert_eq!(key_at(&map, 4), Some(66));
    assert_eq!(key_at(&map, 34), Some(4));
    assert_eq!(map.capacity(), 64);
    assert_eq!(map.len(), 35);
    for k in keys_and(&[64, 66]) {
        assert_eq!(map.get(&k), Some(k), "key {k}");
    }
    assert_eq!(walked_keys(&map), keys_and(&[64, 66]));
}
