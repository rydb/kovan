//! Unit tests of the magazine cache. The depots are process-wide, so every
//! test that goes through them uses a class of its own: tests run on parallel
//! threads, and two of them sharing a class would trade magazines.

use super::*;
use std::collections::HashSet;
use std::vec::Vec;

/// `count` blocks of `class`, from the cache.
fn fresh(class: usize, count: usize) -> Vec<*mut u8> {
    (0..count).map(|_| alloc_block(class)).collect()
}

#[test]
fn every_size_takes_the_smallest_class_that_fits() {
    for size in 1..=1024 {
        let class = class_of(size, 8);
        assert_ne!(class, NO_CLASS, "size {size}");
        assert!(CLASS_SIZES[class] >= size);
        if class > 0 {
            assert!(
                CLASS_SIZES[class - 1] < size,
                "size {size} skips a smaller class"
            );
        }
    }
    assert_eq!(class_of(0, 1), NO_CLASS);
    assert_eq!(class_of(1025, 8), NO_CLASS);
    assert_eq!(class_of(64, 32), NO_CLASS);
    assert_eq!(class_of(16, 16), 0);
}

#[test]
fn class_sizes_keep_every_block_aligned() {
    assert!(CLASS_SIZES.windows(2).all(|w| w[0] < w[1]));
    assert!(CLASS_SIZES.iter().all(|&s| s % CLASS_ALIGN == 0));
    assert!(DEPOT_SLOTS.is_power_of_two());
}

/// A magazine pointer that is only compared, never dereferenced.
fn tag(n: usize) -> *mut Magazine {
    (n * 8) as *mut Magazine
}

#[test]
fn a_ring_hands_magazines_back_in_order_and_answers_full_and_empty() {
    let ring = Ring::new();
    assert_eq!(ring.pop(), None);
    for n in 1..=DEPOT_SLOTS {
        assert_eq!(ring.push(tag(n)), Ok(()));
    }
    assert_eq!(
        ring.push(tag(99)),
        Err(tag(99)),
        "a ring of DEPOT_SLOTS is full"
    );
    for n in 1..=DEPOT_SLOTS {
        assert_eq!(ring.pop(), Some(tag(n)));
    }
    assert_eq!(ring.pop(), None);
}

#[test]
fn a_ring_keeps_working_across_the_wrap_of_its_tickets() {
    // Tickets start 64 short of the end of the word, so 200 turns cross it.
    let ring = Ring::starting_at::<{ 0usize.wrapping_sub(4 * DEPOT_SLOTS) }>();
    let mut next_in = 1;
    let mut next_out = 1;
    for round in 0..200 {
        let pushes = 1 + round % DEPOT_SLOTS;
        for _ in 0..pushes {
            match ring.push(tag(next_in)) {
                Ok(()) => next_in += 1,
                Err(_) => break,
            }
        }
        for _ in 0..1 + (round * 7) % DEPOT_SLOTS {
            match ring.pop() {
                Some(m) => {
                    assert_eq!(m, tag(next_out), "round {round}");
                    next_out += 1;
                }
                None => {
                    assert_eq!(next_out, next_in, "an empty answer with magazines inside");
                    break;
                }
            }
        }
    }
    assert!(
        next_in > 4 * DEPOT_SLOTS + DEPOT_SLOTS,
        "the test never crossed the wrap"
    );
}

#[test]
fn a_freed_block_comes_back_on_the_same_thread() {
    let class = 0;
    let block = alloc_block(class);
    // SAFETY: a fresh block of the class, used by nothing.
    unsafe { free_block(block, class) };
    assert_eq!(alloc_block(class), block);
    // SAFETY: as above.
    unsafe { free_block(block, class) };
}

#[test]
fn one_thread_gets_back_every_block_it_freed_through_both_magazines_and_the_depot() {
    let class = 15;
    let blocks = fresh(class, 5 * ROUNDS);
    for &b in &blocks {
        // SAFETY: fresh blocks of the class, used by nothing.
        unsafe { free_block(b, class) };
    }
    let freed: HashSet<_> = blocks.iter().copied().collect();
    let back: Vec<_> = (0..blocks.len()).map(|_| alloc_block(class)).collect();
    let back_set: HashSet<_> = back.iter().copied().collect();
    assert_eq!(back_set.len(), back.len(), "a block was handed out twice");
    assert_eq!(back_set, freed, "a freed block was not handed back");
    for b in back {
        // SAFETY: blocks of the class this test owns.
        unsafe { free_block(b, class) };
    }
}

#[test]
fn an_exiting_thread_leaves_its_magazines_to_the_next() {
    let class = 16;
    let blocks: Vec<usize> = std::thread::spawn(move || {
        let blocks = fresh(class, 3 * ROUNDS);
        for &b in &blocks {
            // SAFETY: fresh blocks of the class, used by nothing.
            unsafe { free_block(b, class) };
        }
        blocks.into_iter().map(|b| b as usize).collect()
    })
    .join()
    .unwrap();
    // The thread exited: its loaded and previous magazines went to the depot,
    // beside the one it handed over while freeing.
    let freed: HashSet<_> = blocks.iter().copied().collect();
    let back: Vec<_> = std::thread::spawn(move || {
        let back: Vec<usize> = (0..3 * ROUNDS)
            .map(|_| alloc_block(class) as usize)
            .collect();
        for &b in &back {
            // SAFETY: blocks of the class this test owns.
            unsafe { free_block(b as *mut u8, class) };
        }
        back
    })
    .join()
    .unwrap();
    let back_set: HashSet<_> = back.iter().copied().collect();
    assert_eq!(
        back_set, freed,
        "a block the exiting thread cached was lost"
    );
}

#[test]
fn a_full_depot_frees_the_blocks_it_has_no_room_for() {
    let class = 17;
    // The thread's two magazines and the depot's full ring hold this many.
    let cached = (2 + DEPOT_SLOTS) * ROUNDS;
    let blocks = fresh(class, cached + 3 * ROUNDS);
    for &b in &blocks {
        // SAFETY: fresh blocks of the class, used by nothing.
        unsafe { free_block(b, class) };
    }
    let freed: HashSet<_> = blocks.iter().copied().collect();
    let back: Vec<_> = (0..cached).map(|_| alloc_block(class)).collect();
    let back_set: HashSet<_> = back.iter().copied().collect();
    assert_eq!(back_set.len(), cached, "a block was handed out twice");
    assert!(
        back_set.is_subset(&freed),
        "a cached block was not one the thread freed"
    );
    // Everything the cache kept is out now: the next allocation is fresh
    // (the global allocator may hand back an address it was given, so only
    // the count of cached blocks is checked above).
    let next = alloc_block(class);
    for b in back.into_iter().chain([next]) {
        // SAFETY: blocks of the class this test owns.
        unsafe { free_block(b, class) };
    }
}

#[test]
fn producer_and_consumer_threads_trade_blocks_through_the_depot() {
    use std::sync::mpsc;
    let class = 18;
    let (to_consumer, from_producer) = mpsc::sync_channel::<usize>(4 * ROUNDS);
    let rounds = 50 * ROUNDS;
    let consumer = std::thread::spawn(move || {
        for b in from_producer {
            // SAFETY: the producer gave up the block.
            unsafe { free_block(b as *mut u8, class) };
        }
    });
    let mut seen = HashSet::new();
    for i in 0..rounds {
        let b = alloc_block(class);
        // The block is ours until it is sent: write all of it.
        // SAFETY: a block of CLASS_SIZES[class] bytes.
        unsafe { b.write_bytes(i as u8, CLASS_SIZES[class]) };
        seen.insert(b as usize);
        to_consumer.send(b as usize).unwrap();
    }
    drop(to_consumer);
    consumer.join().unwrap();
    // Blocks went around: far fewer distinct addresses than allocations.
    assert!(
        seen.len() < rounds / 4,
        "{} distinct blocks for {rounds} allocations",
        seen.len()
    );
}
