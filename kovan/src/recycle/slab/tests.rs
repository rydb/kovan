//! Unit tests of the slab layer. Each test uses classes no other test (here
//! or in the magazine tests) touches, so the live-chunk counts it reads are
//! its own.

use super::*;
use std::collections::HashSet;
use std::sync::mpsc;
use std::vec::Vec;

fn live(class: usize) -> isize {
    LIVE_CHUNKS[class].load(Relaxed)
}

#[test]
fn chunks_hold_aligned_blocks_inside_them() {
    for (class, &size) in CLASS_SIZES.iter().enumerate() {
        let cap = capacity(class);
        assert!(cap >= 2, "class {class} holds {cap} blocks");
        assert!(HEADER_BYTES + cap * size <= CHUNK_BYTES);
        assert!(HEADER_BYTES >= size_of::<Chunk>());
        assert_eq!(HEADER_BYTES % CLASS_ALIGN, 0);
    }
}

#[test]
fn an_owner_carves_reuses_and_frees_its_chunks() {
    let class = 1;
    let owner = new_owner();
    let mut slab = SlabClass::new();
    let n = 3 * capacity(class) + 5;
    let blocks: Vec<_> = (0..n).map(|_| slab.alloc(class, owner)).collect();
    let set: HashSet<_> = blocks.iter().copied().collect();
    assert_eq!(set.len(), n, "a block was handed out twice");
    for &b in &blocks {
        assert_eq!(b as usize % CLASS_ALIGN, 0);
        let c = chunk_of(b) as usize;
        assert!(
            b as usize >= c + HEADER_BYTES && b as usize + CLASS_SIZES[class] <= c + CHUNK_BYTES
        );
    }
    assert_eq!(live(class), 4);
    for &b in &blocks {
        // SAFETY: blocks of this slab, given back once.
        unsafe { slab.release_own(b) };
    }
    // Every chunk is empty: all but the one kept are freed.
    assert_eq!(live(class), 1);
    // The kept chunk's blocks are handed out again before any new chunk.
    let again: Vec<_> = (0..capacity(class))
        .map(|_| slab.alloc(class, owner))
        .collect();
    assert_eq!(live(class), 1, "a reuse made a new chunk");
    for b in again {
        // SAFETY: as above.
        unsafe { slab.release_own(b) };
    }
    slab.orphan();
    assert_eq!(live(class), 0);
}

#[test]
fn blocks_given_back_by_others_are_handed_out_again() {
    let class = 2;
    let owner = new_owner();
    let mut slab = SlabClass::new();
    let n = 2 * capacity(class);
    let blocks: Vec<usize> = (0..n).map(|_| slab.alloc(class, owner) as usize).collect();
    // Every other block comes back from another thread: no chunk empties.
    let (back, kept): (Vec<usize>, Vec<usize>) =
        blocks.iter().enumerate().partition_map_by_parity();
    let giving = back.clone();
    std::thread::spawn(move || {
        for b in giving {
            // SAFETY: the owner handed these over and does not touch them.
            unsafe { release_remote(b as *mut u8) };
        }
    })
    .join()
    .unwrap();
    // The owner's chunks are exhausted, so its next allocations drain the
    // inbox and hand those blocks out again, without a new chunk.
    let before = live(class);
    let again: HashSet<usize> = (0..back.len())
        .map(|_| slab.alloc(class, owner) as usize)
        .collect();
    assert_eq!(live(class), before, "draining the inbox made a new chunk");
    assert_eq!(again, back.iter().copied().collect());
    for b in again.into_iter().chain(kept) {
        // SAFETY: as above.
        unsafe { slab.release_own(b as *mut u8) };
    }
    slab.orphan();
    assert_eq!(live(class), 0);
}

/// Splits `(index, block)` pairs into the odd-indexed blocks and the even ones.
trait PartitionByParity {
    fn partition_map_by_parity(self) -> (Vec<usize>, Vec<usize>);
}

impl<'a, I: Iterator<Item = (usize, &'a usize)>> PartitionByParity for I {
    fn partition_map_by_parity(self) -> (Vec<usize>, Vec<usize>) {
        let (odd, even): (Vec<_>, Vec<_>) = self.partition(|(i, _)| i % 2 == 1);
        (
            odd.into_iter().map(|(_, &b)| b).collect(),
            even.into_iter().map(|(_, &b)| b).collect(),
        )
    }
}

#[test]
fn an_exited_owners_chunks_are_freed_by_the_last_block_back() {
    let class = 3;
    let (tx, rx) = mpsc::channel::<Vec<usize>>();
    std::thread::spawn(move || {
        let owner = new_owner();
        let mut slab = SlabClass::new();
        let blocks: Vec<usize> = (0..2 * capacity(class) + 1)
            .map(|_| slab.alloc(class, owner) as usize)
            .collect();
        // The owner exits with every block out.
        slab.orphan();
        tx.send(blocks).unwrap();
    })
    .join()
    .unwrap();
    let blocks = rx.recv().unwrap();
    assert_eq!(live(class), 3);
    // Give back every block but one of the first chunk's.
    let first_chunk = chunk_of(blocks[0] as *mut u8) as usize;
    let (keep, rest): (Vec<usize>, Vec<usize>) = blocks.iter().partition(|&&b| b == blocks[0]);
    for &b in &rest {
        // SAFETY: the exited owner handed these over.
        unsafe { release_remote(b as *mut u8) };
    }
    assert_eq!(
        live(class),
        1,
        "a chunk whose blocks all came back was not freed"
    );
    assert_eq!(chunk_of(keep[0] as *mut u8) as usize, first_chunk);
    // SAFETY: as above.
    unsafe { release_remote(keep[0] as *mut u8) };
    assert_eq!(live(class), 0);
}

#[test]
fn blocks_pushed_while_the_owner_exits_are_counted() {
    let class = 4;
    for _ in 0..200 {
        let owner = new_owner();
        let mut slab = SlabClass::new();
        let blocks: Vec<usize> = (0..capacity(class))
            .map(|_| slab.alloc(class, owner) as usize)
            .collect();
        let half = blocks.len() / 2;
        let early = blocks[..half].to_vec();
        let late = blocks[half..].to_vec();
        let giver = std::thread::spawn(move || {
            for b in early {
                // SAFETY: handed over by the owner.
                unsafe { release_remote(b as *mut u8) };
            }
        });
        // Exit while the other thread may be pushing.
        slab.orphan();
        giver.join().unwrap();
        for b in late {
            // SAFETY: as above.
            unsafe { release_remote(b as *mut u8) };
        }
        assert_eq!(live(class), 0, "a chunk outlived its last block");
    }
}

#[test]
fn a_lone_block_frees_its_chunk_when_it_comes_back() {
    let class = 5;
    let b = lone_block(class);
    assert_eq!(live(class), 1);
    // SAFETY: the lone block, given back once.
    unsafe { release_remote(b) };
    assert_eq!(live(class), 0);
}

#[test]
fn threads_giving_blocks_to_each_other_free_every_chunk() {
    let class = 6;
    let threads = 4;
    let (txs, rxs): (Vec<_>, Vec<_>) = (0..threads).map(|_| mpsc::channel::<usize>()).unzip();
    let handles: Vec<_> = rxs
        .into_iter()
        .enumerate()
        .map(|(i, rx)| {
            let next = txs[(i + 1) % threads].clone();
            std::thread::spawn(move || {
                let owner = new_owner();
                let mut slab = SlabClass::new();
                for _ in 0..5_000 {
                    next.send(slab.alloc(class, owner) as usize).unwrap();
                    while let Ok(b) = rx.try_recv() {
                        // SAFETY: handed over by the previous thread.
                        unsafe { release(b as *mut u8, Some((&mut slab, owner))) };
                    }
                }
                drop(next);
                slab.orphan();
                rx
            })
        })
        .collect();
    drop(txs);
    let rxs: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    for rx in rxs {
        for b in rx.try_iter() {
            // SAFETY: every owner exited; these were never given back.
            unsafe { release_remote(b as *mut u8) };
        }
    }
    assert_eq!(live(class), 0, "a chunk was never freed");
}
