# Proofs of kovan

## What is checked, in plain words

Many threads use kovan's data structures at the same time. A bug in that kind of code often
shows up only when the threads' steps happen in one particular order, and a test can run
millions of times without ever hitting that order. A proof does not run the code and hope: it
takes a precise description of the code and checks every case that description allows.

A small example of what that buys. In kovan-map 0.1.20, a remove from the hopscotch map did
its work in two steps: first it emptied the entry's slot, then it cleared the bit that tells
lookups "this slot holds an entry of this bucket". If an insert into the same bucket took the
freed slot between those two steps, it set that same bit, and the remove's second step then
cleared it. The new entry sat in the table where no lookup could ever find it. The model of
the map runs the remove and the insert in every possible order, finds that bad order, and
writes it down step by step (`tla/hopscotch/HS_mut_unguarded_remove_counterexample.txt`).
The code now holds the bucket's writer guard for the whole remove, and the same check finds
no bad order for it.

A second example, checked by both tools below. A hopscotch map with room for 256 entries
holds 40, and a remove leaves 39. That is less than a quarter full, so the map tries to halve
its table: it copies the entries into a table of 128 buckets. Say the keys are such that all
39 want to sit near the same bucket there, where only 32 slots are near enough: the copy finds
an entry it cannot place and is thrown away. It cloned up to 39 entries for nothing. The code
used to try again on the very next remove, and fail again, so a map that kept going up and
down between 39 and 40 entries copied up to 39 entries on every remove. Now the failed shrink
writes down 19 (half of 39) and no remove tries again until fewer than 19 entries are left; a
resize that succeeds, or a clear, erases what was written. The Lean proofs show that between
two such erasures, for one thread doing one operation at a time, all failed shrinks together
copy fewer than 2 * 39 = 78 entries, whatever the operations. With several threads that is
not quite true: inserts can land between a remove's request and its copy, and two removes can
both ask before either shrink fails. What holds there, also proved, is a bound per thread:
each thread's failed copies add up to less than twice its first one plus twice the inserts
after it. The TLA+ model checks the rule and that bound with several threads at once, and
keeps the two older versions of the rule (no threshold at all, and a clear that keeps the
threshold) as mutations that it must catch.

Two tools do the checking, and kovan uses them together. TLA+ looks at many threads at once,
but only for small sizes. Lean looks at one thread at a time, but for every size and every
sequence of operations.

What a check covers is said with it, and nothing beyond: a model checker run covers every
order of steps for the sizes its configuration sets (a few threads, keys and buckets), not
every size; a Lean proof covers every size, for its one-thread model of the code.

## The tools

| tool | what it checks in kovan | how far a check goes |
|------|-------------------------|----------------------|
| TLA+, checked by TLC (`tla/`) | concurrent interleavings: the memory reclamation protocol of `kovan`, and the atomic steps of both maps of `kovan-map` (one step of the model is one atomic step of the code) | every order of every thread's steps, for the threads, keys, buckets and programs each configuration sets |
| Lean 4 (`lean/`) | functional and arithmetic properties, such as thresholds and bounds on the work a sequence of operations causes | every input and every sequence of operations, for a one-thread model of the code |

## How to run them

Every proof runs through the `justfile` at the repository root (`just` lists its recipes):

```sh
just tla hopscotch                  # one TLA+ family: every configuration in proofs/tla/hopscotch
just tla hopscotch HS_shrink_fail   # only the configurations named
just tla-all                        # every TLA+ family
just lean-check-sorry               # fail if a Lean proof has a hole in it (sorry, admit)
just lean                           # build every Lean proof, failing on any warning
just proofs                         # all of the above
```

TLA+: the models need Java on `PATH` (CI uses Java 21); the runner, `proofs/tla/run_tlc.sh`,
fetches the pinned TLA+ tools on first use. A run compares each configuration's result with the
family's `EXPECTED.txt` and exits non-zero on any mismatch. CI runs every family
(`.github/workflows/tla.yml`). `proofs/tla/README.md` lists the models; each family's own
`README.md` explains its model, its configurations and its findings.

Lean: install elan once (`proofs/lean/README.md` says how). The recipes run
`proofs/lean/check.sh`, which CI runs too (`.github/workflows/lean.yml`).

## Coverage

- `tla/reclaim/`: kovan's memory reclamation (pin, the protected load, retire, the traversal,
  flush, a thread's exit and the hand-over of its id, the flush and the exit of a thread that
  never pinned, the recycling of retired nodes), 103 configurations: 44 that must pass and 59
  mutations and witnesses that must fail.
- `tla/chained/`: `kovan_map::HashMap`, the chained map (the link words, the writes, the walks,
  the conditional writes, the freezing migration and clear), 47 configurations: 26 that must
  pass and 21 that must fail.
- `tla/hopscotch/`: `kovan_map::HopscotchMap` (the guarded insert and remove, displacement, the
  conditional writes, the lookup's rescan, resize, clear, the walk across a table swap, the
  shrink a remove asks for, its threshold and the work of failed shrinks per thread), 69
  configurations: 35 that must pass and 34 that must fail.
- `tla/segqueue/`: `kovan_queue::SegQueue` (the claim words and segment pointers, push, pop,
  `try_pop`, the drained head and the head's walk, reclamation of the retired segments), 21
  configurations: 5 that must pass and 16 that must fail.
- `tla/magazine/`: the `recycle` feature's magazine cache (each thread's pair of magazines, the
  depot's two rings at their atomic steps, the refill, the hand-offs, a thread's exit), 20
  configurations: 5 that must pass and 15 that must fail.
- `tla/slab/`: the slab layer under the magazine cache (an owner's chunks and spare, the inbox
  other threads give blocks back on, the drain, the exit's counts, close and count-downs), 15
  configurations: 4 that must pass and 11 that must fail.
- `lean/Kovan/HopscotchShrink.lean`: the hopscotch map's shrink threshold, for one thread and
  every sequence of operations: a successful resize and a clear erase it; after a failed shrink
  at `c` entries, until the next erasure, no shrink is asked for while `max (c / 2) 1` entries
  or more remain, and the first remove below that while the map is underfull asks; between two erasures each failed
  shrink is at fewer than half the entries of the one before, and all of them copy fewer than
  twice the entries of the first.
- `lean/Kovan/HopscotchShrinkThreads.lean`: the same threshold when threads interleave in any
  order: each thread's failed copies add up to less than twice its first plus twice the
  inserts after it, and all failed copies together to at most `W * (2 * (n + I) + 2 * I)` for
  `W` threads making them, `n` entries at the start and `I` inserts; a concrete run shows two
  threads failing at the same count.
- `lean/Kovan/Recycle.lean`: recycling retired nodes, for every sequence of takes, pins, raises,
  loads, retires and frees: with the header re-initialised on every take, no batch skips a reader
  that holds one of its nodes and no reader ever holds a node back in the pool; with the take that
  keeps a stale birth, a concrete run frees a node a reader holds.
- `lean/Kovan/FlushExit.lean`: the flush and the exit of a thread that never pinned, for one
  thread and every sequence of retires, flushes, pins and its exit: exactly when each returns at
  once, claims a tid or runs; every value the thread retired or adopted is submitted or parked
  once it has exited (and with the exit as it was before the fix, a value can be kept nowhere);
  a thread that keeps flushing adopts every chain parked on `maxThreads` tids within
  `maxThreads` flushes.
- `lean/Kovan/SegQueue.lean`: the segment queue's claim words on the code's own masks and shifts:
  a fetch-add never carries the index into the id; positions follow the words, wrap with the ids
  and never go back; `behind` and `classify` on wrapped ids answer as on ids counted without
  wrapping; an `Empty` answer means every cell pushes claimed is behind the head; `len()` is the
  distance from head to tail, or 0 while pops ran ahead.
- `lean/Kovan/Magazine.lean`: the magazine cache's classes (the smallest that fits, aligned to 16),
  the rings' wrapped ticket arithmetic and the slot states it tells apart, the slab layer's chunk
  geometry (a block's masked address is its chunk, every block inside and aligned) and the memory
  bound.
