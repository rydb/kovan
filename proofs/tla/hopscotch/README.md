# The hopscotch map (`HopscotchMap.tla`)

One family of [kovan's TLA+ models](../README.md), which says how to run them and lists the
checks every map model makes ([What the map models check](../README.md#what-the-map-models-check)).

## What is transcribed from the code

- `hopscotch.rs:179` `get` through `hopscotch/table.rs:551` `lookup` (`:593` `find`): G0 (the home's
  control word, one load), G2 (one slot per step), G3 (a miss rereads the word and scans again when
  the move stamp moved).
- `hopscotch.rs:290` `insert_impl` (`insert`, `insert_if_absent` at `:395`, `get_or_insert` at
  `:375`): IW, IC (wait for a resize, the table, the home guard taken without waiting), IS (the
  existence scan and a replace, under the guard), IFr and IL (`displace.rs:101` `link_in`: the
  slot's hop bit published, then the link CAS, the insert's linearization point; a lost slot takes
  the bit back), D0 to D2 and M1 to M4 (`displace.rs:127` `displace`, `:146` `move_toward`, `:192`
  `move_entry`: the moved entry's home guard taken without waiting, the entry linked at its new
  slot, the new bit published with the stamp advanced, the old slot emptied, the old bit cleared at
  the release), DL (the link into the freed slot, through IL), ICnt, IR (the guard released,
  `table.rs:282`, `HomeGuard`'s drop), IA, and NR (no room: the writer resizes itself,
  `hopscotch.rs:354`).
- `hopscotch.rs:442` `remove`: RW, RC, RS and RU (the key's entry unlinked under the guard), RN,
  RR, RT. RS, and IS for an insert, load the words of the slots the home's bits name without
  protecting the entries (`table.rs` `find_held`); RU and IU use those entries a step later (keys
  compared, the value read, the entry unlinked or replaced). The guard's holder is the only thread
  that unlinks or retires an entry of the home, so each entry loaded must still be live at its use
  (`HeldUse`, a use after free otherwise); another thread's step can fall between the load and
  the use.
- `hopscotch/iter.rs:155` `next_entry` (the walk's `next`, `:239`) and `:138` `met_before`: T0, T1, T9 (the walk keeps its table and
  skips a key it met in the lower slots of the key's neighborhood).
- `hopscotch/conditional.rs` (`remove_if` at `:59` and `replace_if` at `:112` through
  `remove_where` at `:302` and `hopscotch.rs:228` `home_of`): RW, RC (a home without bits answers
  absent), CS and CU (the key's entry under the guard, loaded then used as RS and RU load and use
  theirs), CF (the closure, once, reading the entry), CX (the write under the
  guard: the unlink, the replace, or nothing), CR (the release), CT (the retire of an unlinked
  entry), CA. `compute` at `:199`: IW, IC (the guard always), IS and IU (the key's entry: CF), and for an
  absent key IFr, IL, D0 to M4 and DL placing the reserved word (`table.rs:173`
  `Word::reserved`, RSV: a reader and a walk pass it as a free slot, a writer finds it taken) as
  an insert places its entry (`displace.rs:70` `place`), then CF, CX (the reservation filled, or
  given back when the closure makes no entry or panics), CR, CT, CA. A reservation that needs a
  displacement that loses a race, or a resize, releases the guard before the closure runs.
- `hopscotch/resize.rs:97` `try_resize`, `:32` `hold_writers`, `:164` `copy_into`: Z0 to Z4 (every
  home guard taken, the copy into the first free slot of each entry's neighborhood, a neighborhood
  found full doubling the new table of a grow and giving up a shrink, the replaced table's guards
  kept held);
  `hopscotch.rs:461` `clear`: ZX.
- The shrink a remove asks for and its threshold: the table's shrink word
  (`hopscotch/table.rs:432` `Table::shrink_at`, `tb.shk` here), which starts at
  `hopscotch.rs:63` `shrink_at` of the capacity (`table.rs:461`, Fresh). `hopscotch.rs:270`
  `unlink_held` (`:294`, the one compare `prev - 1 < table.shrink_at`): RN, and the remove branch
  of CX for `remove_if` and compute, take the count down and decide whether to ask
  (`AsksShrink`). RQ is the remove's `try_resize(capacity / 2)` once its guard is released and
  its entry retired (`hopscotch/conditional.rs:338`, `:244`): it takes the latch, or returns when
  a resize or a clear holds it, then runs Z1 to Z4 as any resize does and comes back to its
  answer. `resize.rs:141` and `:160`: ZK gives up a shrink whose copy finds a neighborhood full,
  frees the copies with the unpublished table, lowers the old table's word to
  `min(shrink_at(capacity), max(count / 2, 1))` (`:162`) and gives its guards back;
  `resize.rs:148`: ZP publishes a table whose word is its own; `hopscotch.rs:507`: ZX sets the
  word back at the end of a clear. The model keeps the history `recorded` (the threshold the
  last failed shrink wrote since the last publication or clear) beside the word, and
  `ShrinkReset` checks the word is that history folded with the quarter.

Abstractions: a neighborhood of two slots (32 in the code) and move stamps modulo four; a
displacement probes to the end of the padded bucket array (the code stops at 512 slots); an entry
is freed only with its table; the latch is one boolean. `insert_if_absent` and `get_or_insert`
first look the key up (`hopscotch.rs:398`, `:379`) and answer a key found there as a lookup does,
before any guard is taken; the model's claims start at `insert_impl`, so that first lookup is not
modelled. `MinCap` stands for `MIN_CAPACITY` (64 in the code), scaled down as the neighborhood
is; "no threshold" in the history is `ShrinkAny`, one more than the entry pool, so above every
count. Whether a shrink fits is not chosen: the copy computes it (ZK). Every configuration that
predates the threshold sets `MinCap` to its `MaxCap`, so no remove of its programs asks for a
shrink, and each reaches exactly the states it reached before the threshold was modelled.

## The shrink threshold, in plain words

When a remove leaves the table less than a quarter full, the map tries to halve the table: it
copies every entry into a new table of half the size. If an entry finds no free slot near its
bucket there, the copy is thrown away and the table stays as it was. Without a threshold, the
next remove asked for the same shrink again, and a map that stayed at the same size paid for
the same useless copy on every remove. With it, the failed shrink writes half of its entry count
(at least 1) into the table's shrink word, and a remove asks for a shrink again only when the
count it leaves is below that. A resize that publishes its new table starts that table with no
threshold, and a clear writes "no threshold" back. The code keeps one word per table for both
rules (less than a quarter full, and below the threshold), so a remove makes one compare: the
word is the table's quarter, lowered by a failed shrink.

The shrink configurations use a table of sixteen buckets with neighborhoods of two slots,
holding keys 0 and 16 (both of bucket 0, in slots 0 and 1), 5 and 8 (`S_sparse`). Removing key
5 leaves three entries, less than a quarter of sixteen, so the remove asks to shrink to eight
buckets. In eight buckets keys 0, 16 and 8 all belong to bucket 0, whose neighborhood of two
slots holds only two of them, so the copy fails and the threshold becomes 1 (three halved,
rounded down). Inserting and removing key 5 again goes from four entries to three without
asking; only a remove that leaves no entry (below 1) asks again, and an empty map always fits.

The model keeps a history beside the code's threshold: `recorded`, what the last failed shrink
wrote since the last publication or clear, erased by every publication and every clear whatever
the code does. Each remove's decision is checked against it.

- `NoShrinkRetry`: no remove asks for a shrink while the count it leaves is at or above what the
  last failed shrink recorded. In plain words: once a shrink failed, the same shrink is not
  tried again until the map has lost half of the entries it had then, so a map that keeps the
  same size never repeats the failed copy.
- `ShrinkReset`: the map's threshold is always exactly the history. The history is erased at
  every publication and every clear and written only by a failed shrink, so this says that the
  code erases its threshold at exactly those points too, and sets it nowhere else.
- `ShrinkUnblocked`: a remove that leaves the map underfull while no shrink has failed since the
  last publication or clear asks for a shrink. In plain words: an old failure never blocks the
  shrink of a map that a clear emptied and that was filled again.

The two mutations put back the rule as it was before:

- `HS_mut_no_shrink_bound` (`Mutation = "no_shrink_bound"`): no threshold, every remove that
  leaves the map underfull asks for a shrink. TLC's counterexample (55 states): the remove of
  key 5 asks, the shrink fails at three entries; key 5 is inserted and removed again, and that
  remove, at three entries again, asks for the same shrink (`NoShrinkRetry` broken). The keys
  present are the same, so that copy would fail the same way.
- `HS_mut_clear_keeps_bound` (`Mutation = "clear_keeps_bound"`): the threshold without the
  clear's reset. Counterexample (103 states): the shrink fails at three entries (threshold 1);
  the resizer clears the map; keys 1 and 2 are inserted; the remove of key 1 leaves one entry
  of sixteen buckets, underfull, but 1 is not below the old threshold 1, so it does not ask
  (`ShrinkUnblocked` broken). With the reset it asks, and the shrink of that one entry fits.

Three witnesses show the passing configurations reach the cases that matter:
`HS_wit_shrink_given_up` (37 states: a shrink is given up), `HS_wit_shrink_published` (122
states: after the failed shrink at three entries, the removes down to one entry ask for
nothing, the remove that leaves none asks, and its shrink publishes) and
`HS_wit_shrink_after_insert` (37 states, below).

### The work of failed shrinks, with several threads

Each failed shrink cloned up to as many entries as the map held: that is the work the
threshold exists to bound. With several threads two things make the work larger than the
threshold alone suggests, and the model shows both: an insert can land between a remove's ask
and its copy (`HS_wit_shrink_after_insert`), and two removes can both ask before either shrink
has failed, so the second shrink runs on an old ask and fails at the same count as the first
(`HS_wit_shrink_stale_ask`, 85 states: worker 1 removes key 5, leaving three entries, and
asks; worker 2 inserts key 1 and starts removing it, taking its bucket's guard; worker 1's
shrink starts and waits for that guard while worker 2 finishes the remove, leaving three
entries, and asks too, since no threshold exists yet; worker 1's copy fails at three and
writes the threshold 1; then worker 2's shrink runs and its copy fails at three as well,
above that threshold).

What still holds is a bound per worker, the one proved in
`proofs/lean/Kovan/HopscotchShrinkThreads.lean` (`thread_failed_copies_lt_after`). The model
keeps a history, `work`, of every worker's failed copies since the last publication or clear:
the count of its first failed copy, the total of all of them, and the entries counted in
(inserts) since that first one.

- `ShrinkWorkBound`: each worker's failed copies add up to less than twice its first failed
  copy plus twice the inserts since that first one. In plain words: once a worker has paid
  for one failed copy, the rest of its failed copies cost less than that much again, plus two
  entries for every entry inserted meanwhile, so the work grows with the inserts, never with
  the removes. In `HS_shrink_two` both workers' shrinks fail at three entries, and each worker
  stays within its own bound (3 < 2 * 3).
- `HS_mut_no_shrink_bound_work` (`Mutation = "no_shrink_bound"`, the code without the
  threshold): key 5 is removed, inserted and removed again, four times. Every remove asks, and
  every shrink fails at three entries: four failed copies of 3 entries with three inserts
  between them, 12 entries cloned, not below 2 * 3 + 2 * 3 = 12 (`ShrinkWorkBound` broken,
  181 states). With the threshold (`HS_shrink_churn`, the same program) only the first remove
  asks and the bound holds.

## Configurations

Two buckets (homes `k % 2`, neighborhoods of two slots, four slots with the padding) grown to
four, or four shrunk to two; keys 0 to 3. With key 0 in slot 0 and key 1 in slot 1, an insert of
key 2 finds home 0's neighborhood full and moves key 1 to slot 2.

| configuration | programs | resizer | expected |
|---|---|---|---|
| `HS_disp_get` | a move racing lookups of both keys | none | pass |
| `HS_disp_rem` | a move racing a remove of the moved key | none | pass |
| `HS_disp_claim` | two claims of the key whose insert moves another, a claim of the moved key (three workers) | none | pass |
| `HS_disp_iter` | a move racing a walk | none | pass |
| `HS_same_home` | a remove racing an insert into the same home | none | pass |
| `HS_rem_ins` | a `force_remove` racing a replace and a claim of the key | none | pass |
| `HS_stale` | a remove and a re-claim of one key racing a walk | none | pass |
| `HS_claim_grow` | a claim and a replace racing a grow | grow | pass |
| `HS_rem_grow` | a remove, a re-claim and a lookup racing a grow | grow | pass |
| `HS_iter_grow` / `HS_iter_shrink` | a walk racing an insert and a grow / a shrink | grow / shrink | pass |
| `HS_clear` | writes and a lookup racing a clear (a writer grows the table too) | clear | pass |
| `HS_big_disp` | a move, a remove and a re-claim of the moved key, a lookup and a walk (three workers) | grow | pass |
| `HS_big_claims` | two claims of a key whose insert moves another, a `force_remove` of a third (three workers) | grow | pass |
| `HS_live` | a move and a remove of the moved key, weak fairness | none | `Termination` holds |
| `HS_live_reader` | lookups of a key being moved, only the lookups fair (the mover may stop holding a guard or mid-move) | none | `ReaderEnds` holds |
| `HS_live_walker` | a walk with a move in flight, only the walk fair | none | `ReaderEnds` holds |
| `HS_mut_unguarded_remove` | 0.1.20: a remove takes no home guard and clears its bit in the live word | none | `AbsIsContent` broken |
| `HS_mut_unguarded_remove_moved` | the same, racing a move | none | `Linearizable` broken |
| `HS_mut_move_clear_first` | 0.1.20: a move copies the entry, unlinks the original, clears the old bit, then sets the new one, unguarded and with no stamp | none | `Linearizable` broken |
| `HS_mut_no_stamp` | 0.1.20: a lookup that misses never rescans | none | `Linearizable` broken |
| `HS_mut_resize_retry` | 0.1.20: a resize copies without the writer guards, a landed insert retries in the new table | grow | `Exactness` broken |
| `HS_mut_iter_index` | 0.1.20: a walk reloads the current table at every step, keeping its index | grow | `WalkExact` broken |
| `HS_mut_iter_no_recent` | a walk that does not recognize a key it met meets a moved key twice | none | `WalkExact` broken |
| `HS_mut_link_then_publish` | the guard fix merged from `vclq/hopscotch-resize-fixes`: an insert links its entry before it publishes the bit (at the guard's release) | none | `Linearizable` broken |
| `HS_mut_link_then_publish_iter` | the same, as a walk sees it | none | `WalkExact` broken |
| `HS_mut_held_scan` | 0.1.20's unguarded remove racing a claim whose scan under the guard loads the key's entry unprotected | none | `NoUseAfterFree` broken |
| `HS_wit_move` | witness: a move empties its old slot | none | `NoMove` broken |
| `HS_wit_stamp_rescan` | witness: a lookup rescans after a move | none | `NoStampRescan` broken |
| `HS_wit_resize_waits` | witness: a resize waits for a writer holding a home guard | grow | `NoResizeWaitsForWriter` broken |
| `HS_wit_held_home` | witness: a displacement skips a candidate whose home guard is held | none | `NoHeldHomeSkip` broken |
| `HS_wit_walk_skip` | witness: a walk meets a moved key again and skips it | none | `NoWalkSkip` broken |
| `HS_cond_rem` | a `remove_if` racing a replace and a second `remove_if` of the key | none | pass |
| `HS_cond_rpi` | a `replace_if` and a lookup racing a remove and a claim of the key | none | pass |
| `HS_cond_cmp` | computes of one key, present then absent, racing a claim and a remove | none | pass |
| `HS_cond_disp` | a compute of a key whose home's neighborhood is full (it reserves the slot a move frees), racing a lookup and a compute of the moved key | none | pass |
| `HS_cond_unwind` | a compute whose closure panics after its reservation moved a key, racing a lookup and a walk | none | pass |
| `HS_cond_grow` | a compute of an absent key and a `replace_if` racing a grow | grow | pass |
| `HS_cond_clear` | a compute, a `remove_if` and a lookup racing a clear | clear | pass |
| `HS_cond_iter` | a compute that inserts and a `remove_if` of its key racing a walk | none | pass |
| `HS_big_cond` | a compute of the key a displacement is for, a `remove_if` of the key it moves and a claim, a `replace_if` and a lookup (three workers) | grow | pass |
| `HS_live_cond` | computes of a key being moved and a lookup, weak fairness | none | `Termination` holds |
| `HS_live_reader_cond` | a lookup of the key a compute reserved a slot for, only the lookup fair (the compute may stop holding its reservation) | none | `ReaderEnds` holds |
| `HS_mut_unguarded_check` | a conditional write decides on the value a lookup read before it took the home guard, then writes under the guard | none | `CondExact` broken |
| `HS_mut_held_scan_cond` | 0.1.20's unguarded remove racing a `remove_if` whose scan under the guard loads the key's entry unprotected and whose predicate reads it later | none | `NoUseAfterFree` broken |
| `HS_wit_reserved_meet` | witness: a lookup meets a reserved slot | none | `NoReservedMeet` broken |
| `HS_wit_cond_resize` | witness: a resize waits for the home guard a conditional write holds while its closure decides | grow | `NoResizeWaitsForClosure` broken |
| `HS_shrink_fail` | a remove whose shrink fails at three entries, an insert and a remove at that count, removes down to an empty map whose shrink fits (sixteen buckets, one worker) | none | pass |
| `HS_shrink_race` | the failed shrink and an insert and a remove at its count, racing an insert of another key and a lookup | none | pass |
| `HS_shrink_cond` | a `remove_if` whose shrink fails, a compute that inserts the key and one that removes it, racing a lookup | none | pass |
| `HS_shrink_clear` | the failed shrink, then two inserts and a remove that leaves the map underfull, racing a clear | clear | pass |
| `HS_shrink_live` | the programs of `HS_shrink_race`, weak fairness | none | `Termination` holds |
| `HS_mut_no_shrink_bound` | no threshold: every remove that leaves the map underfull asks for a shrink | none | `NoShrinkRetry` broken |
| `HS_mut_clear_keeps_bound` | a clear leaves the threshold a failed shrink wrote | clear | `ShrinkUnblocked` broken |
| `HS_wit_shrink_given_up` | witness: a shrink whose copy does not fit is given up | none | `NoShrinkGivenUp` broken |
| `HS_wit_shrink_published` | witness: after the failed shrink, the remove that empties the map asks, and its shrink publishes | none | `NoRemoveShrinkPublished` broken |
| `HS_wit_shrink_after_insert` | witness: an insert lands between a remove's ask for a shrink and the shrink's copy | none | `NoGrowthBeforeShrink` broken |
| `HS_shrink_churn` | a remove whose shrink fails at three entries, then key 5 inserted and removed three more times at that count | none | pass |
| `HS_shrink_two` | two removers that can both ask for a shrink before either fails | none | pass |
| `HS_mut_no_shrink_bound_work` | no threshold, the program of `HS_shrink_churn` | none | `ShrinkWorkBound` broken |
| `HS_wit_shrink_stale_ask` | witness: a worker's shrink runs on an ask made before another worker's shrink failed, at or above the threshold that failure wrote | none | `NoStaleShrink` broken |
| `HS_mut_unguarded_remove_count` | 0.1.20's unguarded remove, checked against `CountExact` alone: the insert that lands in the freed slot loses its bit, and the count stops matching what a lookup finds | none | `CountExact` broken |
| `HS_mut_held_scan_leak` | the program of `HS_mut_held_scan`, checked against `NoLeak` alone | none | `NoLeak` broken |
| `HS_mut_resize_retry_held` | 0.1.20's resize, which copies without the writer guards, checked against `OldHeld` alone: the replaced table becomes old with its guards down | grow | `OldHeld` broken |
| `HS_mut_unguarded_remove_moved_retired` | 0.1.20's unguarded remove racing a move, checked against `RetiredUnreachable` alone: it retires key 1's entry while the move has it linked at its new slot | none | `RetiredUnreachable` broken |
| `HS_mut_clear_keeps_bound_reset` | a clear that keeps the threshold, checked against `ShrinkReset` alone | clear | `ShrinkReset` broken |
| `HS_mut_insert_skips_lookup` | an insert that does not look for its key's entry links a second one (key 0 inserted again) | none | `NoDuplicate` broken |
| `HS_mut_get_waits_for_guard` | a lookup that waits for its home's writer guard, only the lookups fair (the writer may stop holding it) | none | `ReaderEnds` broken |
| `HS_mut_insert_keeps_guard` | an insert that never releases its home guard, then a remove of the same home, weak fairness | none | `Termination` broken |

## Findings

- **An insert's entry lost to a racing remove of the same home** (`HS_mut_unguarded_remove`, 14
  states). 0.1.20's remove emptied the slot and then cleared the bit with no guard; an insert of
  the same home took the freed slot and set the same bit in between, and the remove's clear left
  the new entry in its slot with no bit naming it: invisible to lookups and removes, and a later
  `get_or_insert` inserted a second one. Racing a move, its unlink CAS failed on the moved entry
  and it answered `None` for a present key (`HS_mut_unguarded_remove_moved`, 20 states). Fix: a remove holds
  the home guard.
- **A lookup missing a key being moved** (`HS_mut_move_clear_first`, 20 states; `HS_mut_no_stamp`, 22 states). 0.1.20
  moved a copy, cleared the old bit before setting the new one, and gave a lookup no way to notice
  a move. Fix: the moved entry's home guard, the same allocation linked at its new slot and named
  by its bit before the old slot empties, and the move stamp a missing lookup rereads.
- **`insert_if_absent` reporting its own insert as present** (`HS_mut_resize_retry`, 28 states).
  Fix: the resize holds every writer guard before it copies, and a landed insert is final.
- **A walk skipping or repeating entries across a resize** (`HS_mut_iter_index`, 32 states). Fix: the walk
  keeps the table it started on (a replaced table keeps its guards held, so its entries stay put).
- **A lookup seeing an insert that a later lookup misses** (`HS_mut_link_then_publish`, 20 states, found in
  `HS_big_disp` while this model was written, then reduced). The guard fix merged from
  `vclq/hopscotch-resize-fixes` linked a new entry before publishing its bit (published at the
  guard's release). A lookup holding a control word read before a remove of the same key cleared
  the slot's bit finds the new entry through that stale bit, while a lookup that starts after it
  answered still misses it: no linearization exists. A walk, which reads slots, yields it the same
  way (`HS_mut_link_then_publish_iter`, 24 states). Fix: the insert publishes the bit before the link CAS
  (`displace.rs:93`), taking it back if the CAS loses the slot.
- **A scan under the guard reading an entry another thread retired** (`HS_mut_held_scan`, 14
  states). A writer's scan under its home guard loads the entries its bits name without
  protecting them, so it relies on no other thread unlinking or retiring one of them before it
  is done. With 0.1.20's remove, which takes no guard, a claim loads the key's entry, the remove
  unlinks and retires it, and the claim then reads the retired entry. A check of the slots at the
  scan alone cannot see this (a retired entry is never in a slot, `RetiredUnreachable`): the load
  and the use are separate steps. Holds with the guard: every remove, replace, move, resize and
  clear of the home's entries holds its guard.

- **A conditional write deciding on a value read outside the guard** (`HS_mut_unguarded_check`,
  15 states).
  A `remove_if` whose predicate ran on the value a lookup returned, then took the home guard and
  unlinked the key's entry, removes a value a replace put there in between, which its predicate
  never saw. Fix: the closure runs under the key's home guard, on the entry the guarded scan
  found (`hopscotch/conditional.rs`). The closure reads that entry after the scan loaded it
  unprotected, a step later, as a claim's scan uses its entry: with 0.1.20's unguarded remove
  unlinking and retiring the entry in between, the closure reads a retired entry
  (`HS_mut_held_scan_cond`, 14 states); with the guard no other thread can.

- **A failed shrink repeated on every remove** (`HS_mut_no_shrink_bound`, 55 states). With no
  threshold, a remove at the count a shrink failed at asks for it again. Fix: a failed shrink
  lowers the table's shrink word to half its count, and a remove asks only below it. A clear that kept
  that threshold blocked the shrink of a map refilled after the clear
  (`HS_mut_clear_keeps_bound`, 103 states); the clear writes "no threshold" back.
- **What the threshold bounds, and what it does not** (`HS_wit_shrink_after_insert`, 37
  states; `HS_wit_shrink_stale_ask`, 85 states). The threshold is checked against the count a
  remove leaves when it asks, not against the count its copy finds: the ask and the copy are
  separate steps. An insert can land between them: in `HS_wit_shrink_after_insert` the remove
  leaves three entries and asks; an insert has already taken its home guard, the shrink waits
  for it (as every resize waits for a guard holder), and once it holds every guard the table it
  is about to copy holds four. And another remove can ask before the first shrink fails, so a
  failed copy can be repeated at the same count once by every thread that had already asked
  (`HS_wit_shrink_stale_ask`). So with several threads the halving of the one-thread proof
  (`proofs/lean/Kovan/HopscotchShrink.lean`) does not hold. What holds is the bound per thread
  proved in `proofs/lean/Kovan/HopscotchShrinkThreads.lean` and checked here as
  `ShrinkWorkBound`: each thread's failed copies stay below twice its first plus twice the
  inserts after it, so all of them together grow with the number of threads and the inserts,
  never with the removes.

## TLC results

The run recorded in `tlc-run.txt` (8 workers for a passing configuration, one for a
violation, beside other work on a 36-core machine): 69 of 69 configurations match `EXPECTED.txt`,
in 192 s of TLC time; the largest passing ones are `HS_big_disp` (4,588,001 distinct states, 65 s)
and `HS_big_cond` (1,444,974, 22 s). The 61 configurations recorded before the mutations for
`NoDuplicate`, `ReaderEnds` and `Termination` and the five single-property runs were added reach
exactly the states (generated and distinct) and give exactly the results they gave before: a
mutation hook changes nothing while its mutation is off. In the same way, every configuration that
passed before the reserved word reaches exactly the states it reached before, the 47 that predate
the shrink threshold exactly those recorded before it was modelled, and the 57 that predate the
work history (`work`) exactly those recorded before it was added (earlier versions of
`tlc-run.txt`).
