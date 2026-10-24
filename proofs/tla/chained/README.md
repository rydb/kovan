# The chained map (`ChainedMap.tla`)

One family of [kovan's TLA+ models](../README.md), which says how to run them and lists the
checks every map model makes ([What the map models check](../README.md#what-the-map-models-check)).

## What is transcribed from the code

Files as of this branch's commit adding the model:

- `hashmap/walk.rs:59` `find`, the writers' walk: F0 (the table), F1 (the head), F2 (a node's
  link word: frozen ends the walk, marked goes to the snip, the key's node is found), F3 (the snip:
  CAS the predecessor from the node to its successor; the thread whose CAS succeeded retires the
  node). `walk.rs:135` `cleanup`, the walk again after a failed unlink (C9).
- `hashmap/walk.rs:146` `lookup` and `:200` `still_links`, the readers' walk: G0 to G3 (a key's
  node answers when its link word is unmarked; a deleted node is stepped past only when the link
  the walk came through, the last live node's, still names the first deleted node of the run
  unmarked, otherwise the walk starts over).
- `hashmap.rs:279` `insert`: I1 to I6 (a new key appended at the tail by one CAS; a present key
  replaced by one CAS that marks the old node's word naming the new node, which names the old
  successor; then the old node unlinked, or the cleanup walk).
- `hashmap.rs:371` `claim` (`insert_if_absent` at `:349`, `get_or_insert` at `:362`): A1 to A9.
- `hashmap.rs:419` `remove` and `:478` `unlink`, `:436` `force_remove`: R1 to R9.
- `hashmap/iter.rs:128` `collect`: T0 to T9 (the walk keeps its table and takes each bucket in one
  validated pass before yielding from it).
- `hashmap/conditional.rs` (`remove_if` at `:57`, `replace_if` at `:110`, `compute` at `:197`,
  `remove_where` at `:262`, `Hold` at `:343`): after the writers' walk, H0 to H3 and H9 (the key's
  node, or for a compute of an absent key the chain's last link, held by one CAS setting its
  HELD flag; the closure run once; the held link written with one store: the mark, the mark
  naming the replacement, a new node at the chain's end, or the word as it was), then the
  remove's R3, R4 and R9 or the insert's I4, I5 and I6. A link word carries the HELD flag (`h`):
  the walk passes it as unheld (F2), every other writer's CAS expects a word without it and
  fails, and the migration's freeze waits for its release (`resize.rs:91`, Z2 and Z3).
- `hashmap/resize.rs:43` `try_resize`, `:72` `clear`, `:91` `freeze`, `:122` `migrate`,
  `:153` `publish`, `:35` `wait_for_resize`: Z0 to Z6 and WT (the latch, every link frozen in chain
  order with the live nodes copied, the new table published with its exact count, the old one
  retired whole; a writer that meets a frozen link waits for the latch and starts over).
- The per-table count (`hashmap/table.rs`, `TableHeader::count`): I5, A5, R3 and Z5.

Abstractions: a table's buckets are a small fixed array; a node is freed only as the table that
owns it is (never individually after a retire, which the model keeps as a state); the latch is
one boolean; `Backoff` is not modelled.

## Configurations

One bucket (every key in one chain) grown to two, or two shrunk to one; keys 1 to 4.

| configuration | programs | resizer | bounds | expected |
|---|---|---|---|---|
| `CM_ins_ins` | insert of a new key, a replace of it | grow | 6 nodes, 2 tables | pass |
| `CM_iia_iia` | `insert_if_absent` and `get_or_insert` of one absent key | grow | 6, 2 | pass |
| `CM_iia_rem` | a claim racing a remove and a re-claim | grow | 8, 2 | pass |
| `CM_ins_rem` | a replace racing a remove | grow | 7, 2 | pass |
| `CM_rem_rem` | adjacent removes and a lookup behind them (three workers) | grow | 6, 2 | pass |
| `CM_frm` | a `force_remove` racing an insert | shrink | 7, 2 | pass |
| `CM_get` | lookups racing a replace and a remove | grow | 7, 2 | pass |
| `CM_iter` | a walk racing a replace, a remove and an insert | grow | 8, 2 | pass |
| `CM_iter_shrink` | the same | shrink | 8, 2 | pass |
| `CM_clear` | writes and a lookup racing a clear | clear | 6, 2 | pass |
| `CM_big_claims` | two claims and a remove of one key (three workers) | grow | 7, 2 | pass |
| `CM_big_iter` | a walk racing a replace and a claim (three workers) | grow | 8, 2 | pass |
| `CM_live` | two removes and a lookup behind them, weak fairness | none | 5, 1 | `Termination` holds |
| `CM_live_reader` | the same, only the lookup scheduled fairly (the removers may stop between a mark and its unlink) | none | 5, 1 | `ReaderEnds` holds |
| `CM_live_walker` | two removes and a walk, only the walk scheduled fairly | none | 5, 1 | `ReaderEnds` holds |
| `CM_mut_retire_on_mark` | 0.1.20: the remover retires the node it marked though its unlink failed | none | 5, 1 | `RetiredUnreachable` broken |
| `CM_mut_no_validate` | 0.1.20: a walk steps past a deleted node without checking it is linked | none | 6, 1 | `NoUseAfterFree` broken |
| `CM_mut_stale_hit` | 0.1.20 and the merged frozen-edge fix: a lookup answers from a deleted node | none | 6, 1 | `Linearizable` broken |
| `CM_mut_revalidate_claim` | 0.1.20: a landed write re-validates and retries in the new table | grow | 5, 2 | `Exactness` broken |
| `CM_mut_revalidate_count` | 0.1.20: the same, for a remove | grow | 5, 2 | `CountExact` broken |
| `CM_mut_two_step_replace` | 0.1.20: a replace marks the old node, then links the new one by a second CAS | none | 6, 1 | `AbsIsContent` broken |
| `CM_mut_two_step_replace_iter` | the same, as a walk sees it | none | 6, 1 | `WalkExact` broken |
| `CM_mut_validate_current` | this branch's first walk: a deleted node validated against the link the walk came through instead of the run's first deleted node, only the lookup fair | none | 5, 1 | `ReaderEnds` broken |
| `CM_mut_validate_current_iter` | the same for a walk | none | 5, 1 | `ReaderEnds` broken |
| `CM_mut_check_addr` | the merged frozen-edge fix: a lookup starts over at every deleted node, with 0.1.20's best-effort unlink | none | 5, 1 | `Termination` broken |
| `CM_wit_failed_snip` | witness: a snip fails and the cleanup walk runs | grow | 6, 2 | `NoFailedSnip` broken |
| `CM_wit_frozen` | witness: a writer meets a frozen link | grow | 6, 2 | `NoFrozenMeet` broken |
| `CM_wit_validation` | witness: a lookup validates its way past a deleted node | grow | 6, 2 | `NoValidationPass` broken |
| `CM_wit_resize_under_write` | witness: a write's CAS is due while a resize holds the latch | grow | 6, 2 | `NoResizeUnderWrite` broken |
| `CM_wit_replace` | witness: a replace reaches its unlink | grow | 7, 2 | `NoReplace` broken |
| `CM_cond_rem` | a `remove_if` racing a replace and a second `remove_if` of the key | grow | 7, 2 | pass |
| `CM_cond_rpi` | a `replace_if` and a lookup racing a remove and a claim of the key | grow | 8, 2 | pass |
| `CM_cond_cmp` | computes of one key, present then absent, racing a claim and a remove | grow | 9, 2 | pass |
| `CM_cond_tail` | a compute of an absent key holding the chain's end racing an insert of another key and a claim of the key | none | 6, 1 | pass |
| `CM_cond_chain` | a compute holding the middle node of a chain of three while the nodes on both sides are removed | none | 5, 1 | pass |
| `CM_cond_clear` | a compute, a `remove_if` and a lookup racing a clear | clear | 6, 2 | pass |
| `CM_cond_iter` | a compute and a `replace_if` racing a walk | grow | 8, 2 | pass |
| `CM_cond_unwind` | a compute of an absent key whose closure panics, racing an insert and a lookup | none | 4, 1 | pass |
| `CM_big_cond` | three conditional writers of one key (compute, `remove_if`, `replace_if`) | none | 5, 1 | pass |
| `CM_live_cond` | a compute holding the middle node, a remove of the node before it, a lookup behind them, weak fairness | none | 5, 1 | `Termination` holds |
| `CM_live_reader_cond` | the same, only the lookup fair (the compute may stop holding its node) | none | 5, 1 | `ReaderEnds` holds |
| `CM_mut_unheld_check` | a conditional write decides on the node it found without holding it, writes by a CAS, and after a lost CAS writes its decision to the node it finds next | none | 6, 1 | `CondExact` broken |
| `CM_wit_held_meet` | witness: a plain write is about to CAS a link a conditional write holds | none | 5, 1 | `NoHeldMeet` broken |
| `CM_wit_freeze_wait` | witness: a migration is about to freeze a held link | grow | 7, 2 | `NoFreezeWait` broken |
| `CM_mut_insert_skips_lookup` | an insert's walk passes over the node of its own key and appends a second one (both workers insert key 1) | grow | 6, 2 | `NoDuplicate` broken |
| `CM_mut_unlink_no_retire` | the remove whose CAS unlinks the node never retires it (a replace and a remove of key 1) | grow | 7, 2 | `NoLeak` broken |
| `CM_mut_revalidate_claim_frozen` | 0.1.20's resize, which does not freeze the links it copies, checked against `OldFrozen` alone | grow | 5, 2 | `OldFrozen` broken |

## Findings: the kovan-map 0.1.20 defects each mutation puts back

- **A node retired while still linked** (`CM_mut_retire_on_mark`, 8 states). 0.1.20's remove marked
  the node, tried its unlink once and retired the node either way. When the unlink failed (the
  predecessor was deleted meanwhile), the retired node stayed in the chain, and a later snip even
  linked its successor through it: a walker loading it after its batch was freed read freed memory.
  Fix: only the thread whose CAS unlinked a node retires it, and a failed unlink runs the cleanup
  walk.
- **A walk through a deleted node's frozen link** (`CM_mut_no_validate`, 25 states). A deleted
  node's `next` is never written again, so the successor it names may have been unlinked and
  retired after the node was; 0.1.20's walks followed it anyway. Fix: step past a deleted node only
  after the link the walk came through still names it unmarked (then the node, and so its
  successor, was reachable when the successor was loaded).
- **A lookup answering a removed value** (`CM_mut_stale_hit`, 19 states). 0.1.20's lookup (and the
  frozen-edge fix merged from `vclq/check-addr`) returned a matching node's value without looking
  at its mark: a lookup that started after a remove returned could answer the removed value. Fix:
  the answer is taken only from a node whose link word it read unmarked.
- **`insert_if_absent` reporting its own insert as present** (`CM_mut_revalidate_claim`, 25
  states) and **a count off by one per race** (`CM_mut_revalidate_count`, 27 states). 0.1.20's
  writers checked after their CAS whether a resize had started, and retried in the new table: a
  claim met its own copied entry there and answered `Some(its own value)`, and a remove removed the
  copy too and counted twice. Fix: the migration freezes every link it copies, so a landed write is
  final and a write that meets a frozen link waits for the new table.
- **A key absent in the middle of a replace** (`CM_mut_two_step_replace`, 9 states;
  `..._iter`, 20 states). 0.1.20 replaced a node by marking it and then linking the new node with a
  second CAS on the predecessor: between the two the key was in no live node, a lookup missed it
  and a walk skipped it. Fix: one CAS marks the old node naming the new one.
- **A lookup that never ends** (`CM_mut_check_addr`, a lasso of 33 states). The frozen-edge fix
  of `vclq/check-addr` made a lookup start over at every deleted node; with 0.1.20's best-effort
  unlink a deleted node can stay linked with no writer left to unlink it, and a lookup of a key
  behind it loops forever. Fix: the validated step past a deleted node, and the cleanup walk.

- **A walk waiting for removers** (`CM_mut_validate_current`, a lasso). This branch's first
  version of the walk validated a deleted node against the link it came through; at the second of
  two adjacent deleted nodes that link names the first, so the walk started over, and kept
  starting over until a remover unlinked one of them: a remover preempted between its mark and
  its unlink held every lookup of the bucket. Found by the shuttle search
  (`kovan-map/tests/shuttle_maps.rs`, `adjacent_removes::hashmap_one_chain`, which reported the
  lookup exceeding shuttle's step bound under PCT), then modelled here with only the reader
  scheduled fairly. Fix: validate against the first deleted node of the run (`walk.rs:200`).

- **A conditional write deciding on a node it does not hold** (`CM_mut_unheld_check`, 23
  states). A closure
  that runs once (an `FnOnce`) cannot be run again on the node that won a lost CAS; a write that
  keeps its decision and applies it to the node it finds next (a replace landed in between)
  removes or replaces a value the closure never saw. Fix: the closure runs while the key's link
  is held (`hashmap/conditional.rs`), so no other write of the key lands between the decision and
  the store that writes it.

## TLC results

The run recorded in `tlc-run.txt` (8 workers for a passing configuration, one for a
violation, beside other work on a 36-core machine): 47 of 47 configurations match `EXPECTED.txt`,
in 1207 s of TLC time; the largest passing ones are `CM_rem_rem` (10,004,502 distinct states,
272 s), `CM_big_iter` (7,974,721, 226 s), `CM_big_claims` (3,260,753, 90 s) and `CM_big_cond`
(854,360, 22 s). The 44 configurations recorded before the mutations for `NoDuplicate` and
`NoLeak` and the `OldFrozen` run were added reach exactly the states and give exactly the results
they gave before, except the two liveness mutations `CM_mut_validate_current` and
`CM_mut_validate_current_iter`: they break `ReaderEnds` as before, but TLC checks liveness on
the part of the state space explored so far at intervals, so where it stops, and the count it
stops at, varies from run to run. Every configuration that passed before the held flag reaches
exactly the states it reached before (the flag is never set without a conditional write). A
variant of `CM_big_cond` racing a grow (7 nodes, 2 tables) passed too, with 51,695,290 distinct
states in 585 s; it is left out of `EXPECTED.txt` for the time it would add to every run.
