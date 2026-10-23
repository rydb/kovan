# The magazine cache (`Magazine.tla`)

One family of [kovan's TLA+ models](../README.md), which says how to run them.

## What is transcribed from the code

kovan's magazine cache for one size class (`kovan/src/recycle.rs`, the `recycle` feature): each
thread's `loaded` and `previous` magazines, and the depot's two rings of full and empty magazines,
each a Vyukov ring of `SLOTS` slots modelled step by step (the ticket loaded, the slot's turn word
read, the ticket's compare-and-swap, the magazine stored, the turn published; and for a pop the
magazine read, then the slot handed to the next round).

- An allocation pops from `loaded`; finding it empty, it swaps with a full `previous`, or loads a
  full magazine from the depot (handing the drained one to the empty ring), or refills: an empty
  magazine loaded first (from the empty ring, or a new one), then `BATCH` blocks from the layer
  below, one handed out and the rest in `loaded`.
- A free pushes on `loaded`; finding it full, it swaps with an empty `previous`, or hands a full
  `previous` to the full ring (giving its blocks back to the layer below when the ring has no
  room) and loads an empty magazine.
- An exit hands both magazines back: one with blocks to the full ring (its blocks to the layer
  below when there is no room), an empty one to the empty ring (freed when there is no room).

What is left out or folded, and why it changes nothing:

- The layer below the magazines, the slab layer, is a set of free blocks here (`pool`): its own
  protocol is [the slab family](../slab/README.md).
- Tickets are counted without wrapping; `proofs/lean/Kovan/Magazine.lean` proves the wrapped
  arithmetic decides as the unwrapped one does.
- A thread's work on its own magazines between two ring operations is one step: no other thread
  sees it.
- Threads run scripted programs (`Prog`) as well as programs of any operations (`Ops`), with any
  interleaving either way: a script reaches the deep cases (a ring filling, two pops racing for
  one magazine) that an open program of the same length cannot reach in a search of reasonable
  size.
- A step that takes a free block, or one of the blocks a thread holds, takes the lowest-numbered
  one. Those blocks are named nowhere else (`BlockOnce`), blocks are only compared for equality,
  and a refill puts at most one block into a magazine (`BATCH` is 1 or 2, an `ASSUME`), so taking
  another is the same step with two blocks' names swapped: the states checked are every state
  any choice reaches, up to the names of the blocks, without the copies that differ only in
  names. (It only narrows the choices, so every violation it finds the unnarrowed model has too.)
- A hand-over goes to a thread between two of its operations; once every other thread is past
  its program, the thread frees the block itself, as a program does whose consumers are gone.

## Properties

- `MagOnce`: every magazine is in exactly one place (a thread's pair, its hand, a ring's
  published slot), or is one no one has, empty.
- `BlockOnce`: every block is in exactly one place: the layer below, a thread's live nodes, a
  free in progress, or one position of one magazine.
- `Handover`: a pop about to read its slot finds the magazine the push of its ticket stored.
- `FullHoldsBlocks`: the full ring holds only magazines with blocks.
- `Bounded`: no magazine holds more than `ROUNDS` blocks, and no thread more than its pair and
  one magazine in hand.
- `PairShape`: between two operations, `loaded` is NULL only while `previous` is, and `previous`
  is NULL, empty or full.
- `ExitReturns`: once every thread has exited, none keeps a magazine or a block.
- `Termination`, under fairness: every operation and every exit ends.

## Mutations and witnesses

| configuration | the wrong rule | expected |
|---|---|---|
| `MG_mut_pop_no_claim` | a pop takes its ticket with a plain store, not a compare-and-swap | `MagOnce` broken |
| `MG_mut_push_turn_first` | a push publishes the turn before storing the magazine | `Handover` broken |
| `MG_mut_exit_forgets_previous` | an exit drops its previous magazine | `MagOnce` broken |
| `MG_mut_release_leaks` | a magazine the full ring has no room for has its blocks dropped | `BlockOnce` broken |
| `MG_mut_empty_to_full` | an exit hands an empty magazine to the full ring | `FullHoldsBlocks` broken |
| `MG_mut_swap_full_previous` | a free swaps with a full previous magazine | `Bounded` broken |
| `MG_mut_pop_previous_in_place` | an allocation takes a block from a full previous in place | `PairShape` broken |
| `MG_mut_exit_keeps_loaded` | an exit keeps its loaded magazine | `ExitReturns` broken |
| `MG_mut_stale_ticket` | a ring operation retries a taken ticket forever | `Termination` broken |

Each lists its property first, so TLC names it. The witnesses show the passing configurations
reach an allocation from the depot (`MG_wit_depot_pop`), a full ring (`MG_wit_depot_full`), a
refill (`MG_wit_fresh`), a new magazine (`MG_wit_new_magazine`), a ring going round more than once
(`MG_wit_wrap`), and the depot holding full magazines after every thread exited
(`MG_wit_exit_to_depot`).

## Configurations

| configuration | threads | programs |
|---|---|---|
| `MG_two` | two | one runs two operations of any kind, the other allocates then frees |
| `MG_trade` | two | a producer hands two nodes to a consumer that allocates two and frees all four |
| `MG_race` | three | one fills the depot at its exit while two allocate from it, so two pops race for one magazine |
| `MG_rounds` | two | magazines of two blocks and refills of two: seven operations and six |
| `MG_live` | two, fair | exits with three full magazines between them; `Termination` |

Magazines of one block and rings of two slots unless said otherwise. The magazines that can exist
(`NMags`) are kept few, since each spare one multiplies the states by the choice of which a new
magazine takes; a step that finds no block or no magazine left cannot run, so a pool too small
for some interleaving shows as a deadlock, never as a pass.

## Code map

| label | function | code | step |
|---|---|---|---|
| `RP1`-`RP5` | `Ring::push` | `recycle.rs:249-274` | ticket, turn word, the ticket's CAS, the magazine, the turn |
| `OP1`-`OP5` | `Ring::pop` | `recycle.rs:277-302` | ticket, turn word, the ticket's CAS, the magazine, the next round's turn |
| `GE1`, `GE2` | `Depot::give_empty` | `recycle.rs:326-331` | the empty ring, or the magazine freed |
| `GB1`, `GB2` | `Depot::give_back` | `recycle.rs:336-346` | the full ring, or the blocks below and the magazine to the empty ring |
| `AL1` | `Pair::pop`, `Pair::pop_slow` | `recycle.rs:394-430` | `loaded`, or a swap with a full `previous`, or the full ring |
| `AL2`, `AL3` | `Pair::pop_slow` | `recycle.rs:408-430` | load the depot's full magazine; the drained one to the empty ring |
| `AL2b`, `AL2c` | `Pair::refill` | `recycle.rs:436-453` | an empty magazine loaded, then a batch from the slab layer |
| `FR1`-`FR4` | `Pair::push`, `Pair::push_slow` | `recycle.rs:457-500` | `loaded`, a swap, `previous` to the depot or its blocks below, an empty magazine |
| `EX1`-`EX3` | `ThreadCache::drop` | `recycle.rs:548-560` | both magazines handed back |

## TLC results

The run recorded in `tlc-run.txt` (4 workers for a passing configuration, one for a
violation, at the lowest priority on a 36-core machine shared with other heavy work): 20 of 20
configurations match `EXPECTED.txt`, in 1659 s of wall time. The passing ones are `MG_race`
(47,740,142 distinct states, 996 s), `MG_trade` (5,261,842, 104 s), `MG_two` (2,161,034, 56 s),
`MG_live` (1,563,754, 100 s, with `Termination`) and `MG_rounds` (504,070, 13 s). The longest runs
that break a property, on one worker, are `MG_mut_stale_ticket` (1,021,716 distinct states, 194 s)
and `MG_mut_pop_no_claim` (1,243,628, 163 s). `MG_mut_stale_ticket` breaks a liveness property,
which TLC checks at intervals on the part of the state space explored so far, so the count it stops
at varies from run to run (CI's run of the same model stopped at 1,304,519).
