# Lean proofs of kovan

## What this is, in plain words

Lean is a program that checks proofs. We write down a fact about a small, exact model of one
piece of kovan ("after this happens, that can never happen"), then a proof of it, step by
step, and Lean checks every step. If one step does not follow from the ones before, the build
fails. A test tries some inputs; a checked proof covers every input its statement allows, of
any size.

The models here are sequential: one thread doing one operation at a time. That suits facts
about arithmetic and bookkeeping, such as a threshold or a bound on how much work any sequence
of operations can cause. How threads interleave is checked by the TLA+ models in `../tla/`.

### The first proof: the hopscotch map's shrink threshold

A `HopscotchMap` keeps its entries in a table of buckets. Take a table of 256 buckets holding
40 entries: 20 whose keys belong to bucket 0 and 20 whose keys belong to bucket 128 (the test
`a_failed_shrink_does_not_recopy_the_table_on_every_remove` in
`kovan-map/src/hopscotch/tests.rs` builds exactly this map).

1. A remove leaves 39 entries. That is less than a quarter of 256 (64), so the remove asks to
   halve the table to 128 buckets.
2. In 128 buckets, bucket 0 and bucket 128 become the same bucket, so all 39 entries want to
   sit near bucket 0. Only 32 slots are near enough (the neighborhood), so the copy finds an
   entry it cannot place, throws the new table away, and keeps the old one. The copy cost up
   to 39 clones of a key and a value, for nothing.
3. What used to happen: the next remove asked for the same shrink and failed the same way. A
   map that went up and down between 39 and 40 entries paid for that useless copy on every
   remove, for as long as it ran.
4. What happens now: the failed shrink writes down 19 (39 halved, rounded down). No remove
   asks for a shrink again until fewer than 19 entries are left. The map can go up and down
   between 39 and 40 entries forever without copying anything. In the test, removes then
   bring it down to 18 entries: that remove asks again, the 18 entries fit, and the table
   becomes 128 buckets.
5. In the worst case, shrinks keep failing: at 39, then at fewer than 19, then at fewer than
   half of that, and so on. Each failure is at less than half the entries of the one before,
   so all the failed copies together clone fewer than 2 * 39 = 78 entries, until a resize
   succeeds or the map is cleared.

`Kovan/HopscotchShrink.lean` proves steps 4 and 5 (the code as it is now; step 3 is the old
code, which it does not model) for every sequence of inserts, removes, grows and clears, and
for every outcome of every shrink (it does not place entries in buckets, so the outcome of
each shrink is left open: fits or does not fit, except that an empty map always fits). It does
not prove step 2 (which keys fit where), and it is about one thread doing one operation at a
time.

### With several threads

With several threads, step 5 is not true as stated, for two reasons, and
`Kovan/HopscotchShrinkThreads.lean` proves what is true instead.

- A remove asks for its shrink first and the shrink copies the map a moment later, after the
  remove has let go of its bucket. Inserts by other threads can land in between: the remove
  left 3 entries, the copy finds 4.
- Two threads can each remove an entry and each ask before either shrink has run. The first
  shrink fails and writes its threshold, but the second thread asked before that threshold
  existed, so its shrink runs too and fails at the same count. The file checks a run where
  this happens (`two_threads_fail_at_the_same_count`).

What holds is a rule per thread: each thread's failed copies add up to less than twice its
first failed copy plus twice the number of inserts after it. A thread whose first failed copy
is at 39, with 10 inserts after it, clones fewer than 2 * 39 + 2 * 10 = 98 entries in all its
failed copies. Adding up the threads: all failed copies together are at most the number of
threads that made one, times twice the most entries the map can hold in the run (the count at
the start plus the inserts) plus twice the inserts. With 4 threads, 40 entries at the start
and 10 inserts, that is at most 4 * (2 * 50 + 2 * 10) = 480 entries, until a resize succeeds
or the map is cleared. Before the threshold there was no such bound at all: the total grew
with every remove.

The model there lets the steps of all threads come in any order, lets a remove ask whenever
the threshold allows (the code also needs the table underfull), and includes a failed resize
that no remove asked for (an insert's grow whose table another grow had already replaced by a
larger one). That last kind writes the threshold like any failed shrink but is not counted in
the bound: no threshold holds it back. The TLA+ model in `../tla/hopscotch` checks the per
thread rule, as `ShrinkWorkBound`, in its configurations with several threads.

### The second proof: flush and exit on a thread that never pinned

A thread gets a thread ID (a tid) the first time it pins. Take thread B, which never pins: it
only drops `Removed` values another thread handed it, and each such drop retires the value
without a pin. B has no tid, and the values wait in its batch. Elsewhere, thread A exits with
a batch it cannot place and parks it on its tid, as a chain for a later `flush()` to adopt.

1. What used to happen: B's `flush()` returned at once because B had no tid, and so did B's
   exit. B's values were never submitted, so never freed, and A's chain was never adopted by B.
2. What happens now: B's `flush()` claims a tid, as a first pin does, when its own batch holds
   a value or some tid holds a parked chain; then it adopts one chain and submits its batch.
   With nothing to do it still returns at once and claims nothing. B's exit, finding no tid and
   a value in its batch, claims a tid and runs the exit every thread runs: submit, park what
   cannot be placed, release the tid.
3. So, whatever B does (retire, flush, pin, then exit) and whatever happens to each
   submission, every value B retired or adopted is submitted or parked once B has exited.
4. And a B that keeps flushing adopts every chain parked on any of `maxThreads` tids within
   `maxThreads` flushes, so within `maxThreads + 1`.

`Kovan/FlushExit.lean` proves steps 2 to 4 for the code as it is now, and shows step 1 for
the old exit: with it, a thread that retires one value and exits keeps it nowhere. It models
one thread doing one operation at a time; the TLA+ model in `../tla/reclaim` checks the same
paths with several threads (`RC_unpinned_retire`, `RC_wf_unpinned_exit`,
`RC_wf_unpinned_flush`, `RC_flush_orphan`, and the mutations that put the old returns back).

## What is proved

`Kovan/HopscotchShrink.lean`, a model of `kovan-map/src/hopscotch.rs` (`shrink_at`,
`unlink_held`, `clear`), `kovan-map/src/hopscotch/table.rs` (`Table::shrink_at`) and
`kovan-map/src/hopscotch/resize.rs` (`try_resize`): a map is its count, its capacity and its
threshold (with a case of its own, `unset`, for "no threshold"); the operations are an insert, a
remove (given whether the shrink it may ask for fits), a grow and a clear. The code folds the
threshold and the quarter-full test into one word of the table; `word` computes it from the
model, and `asks_iff_below_word` with `word_gaveUp`, `word_published` and `word_cleared` prove
the fold exact, so the theorems hold of the code as written.

| theorem | what it says |
|---------|--------------|
| `published_erases` | a resize that publishes its new table leaves no threshold |
| `grow_erases` | a grow leaves no threshold |
| `clear_erases` | a clear leaves no threshold and no entry |
| `erasure_erases` | every operation whose outcome is a published shrink, a grow or a clear leaves no threshold |
| `failed_shrink_records` | right after a shrink fails at `c` entries, the threshold is `max (c / 2) 1` |
| `remove_asks_iff` | with threshold `b`, a remove asks for a shrink exactly when it leaves fewer than `b` entries and the map underfull |
| `no_shrink_while_at_least` | with threshold `b`, a run of inserts and removes that never leaves fewer than `b` entries asks for no shrink and keeps the threshold `b` |
| `first_remove_below_asks` | with threshold `b`, a remove that leaves fewer than `b` entries while the map is underfull asks for a shrink |
| `after_failed_shrink` | after a shrink fails at `c` entries, any run of inserts and removes that stays at `max (c / 2) 1` entries or more asks for no shrink, and the next remove below that while the map is underfull asks |
| `unset_remove_asks_iff` | with no threshold (after a clear, say), a remove asks for a shrink exactly when it leaves the map underfull |
| `failed_shrinks_halve` | between two erasures, each failed shrink happens at fewer than half the entries of the one before |
| `failed_shrink_copies_below_twice_first` | between two erasures, the failed shrinks together happened at fewer than twice the entries of the first one, so they clone fewer than that many entries in total |
| `asks_iff_below_word` | the code's one compare (`count < table.shrink_at`) asks for a shrink exactly when the two tests above do (underfull, and below the threshold if there is one) |
| `word_gaveUp`, `word_published`, `word_cleared` | a failed shrink, a publication and a clear leave exactly the word the code writes (the quarter lowered to the threshold, the new table's quarter, the quarter) |

`Kovan/HopscotchShrinkThreads.lean`, the same rule when threads interleave: a state is the
count, the threshold and, for each thread, whether it asked for a shrink that has not run yet;
the events are an insert, a remove by a thread (which may ask), a thread's shrink whose copy
fails, a thread's shrink skipped because another resize holds the `resizing` flag, and a failed
resize no remove asked for. The theorems are about any run between two erasures.

| theorem | what it says |
|---------|--------------|
| `two_threads_fail_at_the_same_count` | a concrete run where two threads' shrinks both fail at the same count, so the one-thread halving rule does not hold across threads |
| `thread_failed_copies_lt_after` | each thread's failed copies add up to less than twice its first failed copy plus twice the inserts after that first one |
| `thread_failed_copies_lt` | the same, with all the inserts of the run |
| `failuresOf_le` | every failed copy is at most the count at the start plus the inserts of the run |
| `total_le_sum_threads` | all failed copies together are at most the sum, over a list of threads covering them, of each thread's failed copies |
| `failed_copies_le` | all failed copies together are at most the number of threads that made one, times twice (the count at the start plus the inserts) plus twice the inserts |
| `one_thread_failed_copies_lt` | when one thread makes all the failed copies, they add up to less than twice the first one plus twice the inserts |

Both files explain every definition and every proof step in plain words, with a small example
for each statement. Every theorem rests only on Lean's own axioms (`propext`, `Quot.sound`,
`Classical.choice`), or on none: `check.sh axioms` checks it for every theorem of the library.

`Kovan/FlushExit.lean`, a model of `kovan/src/guard.rs` (`Handle::flush`, `Handle::cleanup`,
`retire`, `pin`) and `kovan/src/slot.rs` (`adopt_orphans`, `orphans_parked`): the start of
each of flush and exit is a function of what the handle tells it (a tid or not, an empty batch
or not, a chain parked or not, the exit still to run or not, inside a reclamation or not); a
run is one thread's retires, flushes, pins and exit, each submission placed or not as the run
chooses, over the orphan words of every tid.

| theorem | what it says |
|---------|--------------|
| `flush_returns_iff` | `flush()` returns at once exactly when the thread has no tid and either nothing to submit or adopt or its exit already ran, or when it runs inside a reclamation |
| `flush_claims_iff` | `flush()` claims a tid exactly when the thread has none, runs outside any reclamation before its exit, and has a value in its batch or finds a chain parked |
| `flush_runs_iff` | `flush()` runs with the tid it has exactly when the thread has one, outside any reclamation |
| `flush_idle_claims_none` | a flush with no tid, an empty batch and nothing parked claims no tid |
| `exit_returns_iff`, `exit_claims_iff`, `exit_runs_iff` | the exit returns at once exactly with no tid and an empty batch, claims a tid exactly with no tid and a value in its batch, and runs exactly with a tid |
| `leak_free` | once the thread has exited, every value it retired or adopted, over any run, is submitted or parked |
| `retired_is_kept` | every value the thread retires before its exit is submitted or parked once it has exited |
| `old_exit_loses` | with the exit as it was before the fix, a thread that retires one value and exits keeps it nowhere |
| `adopted_within_max_threads` | a thread that has not exited, with a tid or not, empties every orphan word of `maxThreads` tids within `maxThreads` flushes |
| `adopted_within` | the same within `maxThreads + 1` flushes |

All of them use only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`), or
none; `#print axioms` lists them.

The file explains every definition and every proof step in plain words.

## How to check it

The toolchain is pinned in `lean-toolchain` (Lean 4 v4.35.0, core Lean only: no Mathlib, no
other package). Install elan, the Lean toolchain manager, once:

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none
```

(`just lean` also finds lake in `~/.elan/bin` when it is not on `PATH`). Then, from the
repository root:

```sh
just lean-check-sorry    # fails if `sorry` or `admit` (a hole in a proof) appears
just lean                # `lake build --wfail`: every proof, failing on any warning
just lean-check-axioms   # fails if a theorem rests on an axiom other than Lean's own three
```

All three run `check.sh` in this directory (`bash proofs/lean/check.sh sorry`, `... build` and
`... axioms`; with no argument it runs all three). The axiom check compiles `Axioms.lean`, which
walks every theorem whose name starts with `Kovan` and collects the axioms it rests on, through
every lemma it uses: a proof with a hole rests on `sorryAx`, and one that ran compiled code on
`Lean.ofReduceBool`, so either fails it. It finds the theorems itself, so a new one is checked
without being listed anywhere.

The first build downloads the pinned Lean release. CI runs the same three checks
(`.github/workflows/lean.yml`), with an elan release pinned by its SHA-256.
