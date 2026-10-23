# The slab layer (`Slab.tla`)

One family of [kovan's TLA+ models](../README.md), which says how to run them.

## What is transcribed from the code

The slab layer under the magazine cache for one class (`kovan/src/recycle/slab.rs`): one owner
thread's chunks of `CAP` blocks, its inbox, and releaser threads it hands blocks to (the nodes of a
structure other threads free).

- The owner allocates from a chunk with a block to hand out (its free list, or carving); with none,
  it drains its inbox (a swap) back into the chunks' free lists, or makes a chunk. A block back
  to its own chunk goes on the free list; an emptied chunk is freed unless it is kept as the
  class's one spare.
- A releaser gives a block back by reading the chunk's inbox pointer and pushing the block on the
  inbox with a compare-and-swap; finding the inbox closed, it counts the chunk down, and the last
  block back frees the chunk (and, with the last reference, the inbox).
- The owner's exit drains the inbox, writes each chunk's count of blocks out (freeing the empty
  ones), closes the inbox with a swap, counts down for the blocks pushed in between, and gives up
  its reference to the inbox.

Every access to a chunk or to the inbox is checked against those already freed. Chunks are
named by fresh ids, so an access to a freed one is never mistaken for one to a new chunk at the
same address.

## Properties

- `NoUseAfterFree`: no thread touches a freed chunk or a freed inbox.
- `BlockOnce`: every carved block of a live chunk is in exactly one place: a thread, a releaser
  giving it back, the inbox, the owner's collected blocks, the chunk's free list, or counted back
  into an orphaned chunk.
- `BlocksOfFreed`: no block of a freed chunk is held, given back, in the inbox or collected.
- `UsedRight`: while the owner runs, a chunk's count of blocks out is right.
- `CountsRight`: once written at the exit, a chunk's count is its blocks out, and positive.
- `NoLeak`: once every thread is done, every chunk and the inbox are freed.
- `Termination`, under fairness.

## Mutations and witnesses

| configuration | the wrong rule | expected |
|---|---|---|
| `SL_mut_close_before_counts` | the exit closes the inbox before writing the counts | `CountsRight` broken |
| `SL_mut_touch_after_push` | a releaser reads the chunk after its push | `NoUseAfterFree` broken |
| `SL_mut_drop_closed_blocks` | the close drops the blocks it collected | `BlockOnce` broken |
| `SL_mut_free_one_early` | the owner frees a chunk with one block still out | `BlocksOfFreed` broken |
| `SL_mut_keep_inbox_ref` | freeing a chunk keeps its reference to the inbox | `NoLeak` broken |
| `SL_mut_stale_head` | a releaser retries its compare-and-swap with the old head | `Termination` broken |

The witnesses show the passing configurations reach a remote push (`SL_wit_remote_push`), a
releaser counting down after the owner exited (`SL_wit_count_down`), a releaser freeing a chunk
(`SL_wit_freed_by_releaser`), a spare chunk (`SL_wit_spare`), and a block handed out again from a
fully carved chunk (`SL_wit_reuse`).

## Configurations

| configuration | releasers | owner operations, chunks |
|---|---|---|
| `SL_two` | two | nine, three chunks |
| `SL_one` | one | eight, three chunks |
| `SL_deep` | two | ten, four chunks |
| `SL_live` | two, fair | three; `Termination` |

Chunks of two blocks in every one.

## Code map

| label | function | code | step |
|---|---|---|---|
| `OW1` (alloc) | `SlabClass::alloc` | `slab.rs:237-269` | a free-list block, a carved one, or the chunk off the partial list |
| `OW1` (drain), `OW2`, `OW2s` | `SlabClass::drain_inbox`, `settle` | `slab.rs:291-331` | the inbox swapped, each block to its chunk, an empty chunk freed or kept |
| `OW1` (new chunk) | `SlabClass::new_chunk` | `slab.rs:334-377` | a chunk made, its inbox reference taken |
| `OW1` (give back), `OW3` | `SlabClass::release_own`, `settle` | `slab.rs:277-312` | a block back to its own chunk |
| `RR1`, `RR2` | `release_remote` | `slab.rs:492-516` | the chunk's inbox, the inbox word, the push's CAS |
| `RR4` | `count_down`, `free_chunk`, `release_inbox` | `slab.rs:477-483`, `slab.rs:193-206`, `slab.rs:106-112` | the count-down; the last frees the chunk and maybe the inbox |
| `EX1`-`EX6` | `SlabClass::orphan` | `slab.rs:432-469` | the drain, the counts, the close and its count-downs, the owner's reference |

## TLC results

The run recorded in `tlc-run.txt` (4 workers for a passing configuration, one for a violation, at
the lowest priority on a 36-core machine shared with other heavy work): 15 of 15 configurations
match `EXPECTED.txt`, in 40 s of wall time. The passing ones are `SL_deep` (1,885,607 distinct
states, 19 s), `SL_two` (390,403, 6 s), `SL_one` (23,197, 2 s) and `SL_live` (535, 1 s, with
`Termination`). Every mutation breaks its property within 1,393 distinct states
(`SL_mut_free_one_early`) and two seconds.
