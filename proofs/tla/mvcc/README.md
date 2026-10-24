# The multi-version concurrency control (`Mvcc.tla`)

One family of [kovan's TLA+ models](../README.md), which says how to run them.

## What is transcribed from the code

`kovan-mvcc` (`kovan-mvcc/src/percolator.rs`, `storage.rs`, `timestamp_oracle.rs`) at the grain
of its atomic steps: the timestamp oracle, the three column families of `InMemoryStorage` (each
key's lock, its records by `commit_ts`, its data by `start_ts`), the two registries, the SSI
commit lock, and the transactions. Each process is one transaction running a fixed program
(`MC_Mvcc.tla`): its isolation level, its reads, writes and deletes in order, and its end, a
commit or a drop. Values are the writing transaction's id, and a setup transaction 0 committed
the keys a configuration seeds (start 1, commit 2).

- `begin_with_isolation` registers the transaction in `ActiveTxnRegistry` under the instance's
  greatest timestamp taken so far (`issued`, a bound below every later one), takes `start_ts` from
  the oracle, `counter.fetch_add(1) + 1` (recording it in `issued`), and registers it again under
  `start_ts`, the entry replaced.
- `write` and `delete` only buffer; the first key written is the primary. A read of a buffered
  key answers the buffer.
- `read` takes `read_ts` (a fresh timestamp under ReadCommitted, `start_ts` otherwise) and loads
  the key's lock. For a lock of a transaction that started at or before `read_ts` it backs off and
  looks again, or gives up and answers `Err(LockConflict)` (`BackoffAction::Abort`). Otherwise it
  loads the latest Put or Delete record at or before `read_ts` (`get_latest_commit`), then the
  data at the `start_ts` that record names (`get_data`); data that is gone is
  `Err(StorageError)`. A Serializable read puts the key in its read set on every path.
- `commit` prewrites. Pass 1 takes each key's lock in
  sorted order with `insert_if_absent` (another transaction's lock is a `LockConflict`). Pass 2
  loads each key's latest record of any kind and rejects a Rollback record or a commit at or
  after `start_ts`. Pass 3 writes the data at `start_ts`. A failed pass releases the locks it
  took, one `delete_lock` each, and `commit` calls `rollback`. A Serializable transaction then
  takes `ssi_commit_lock` and validates its read set: a key whose latest Put or Delete
  (`get_latest_commit`) is after `start_ts` fails it (`SerializationFailure`) and `rollback` runs.
  Then `commit_ts`
  from the oracle. `commit_primary` loads the primary's lock, writes its record, deletes its lock;
  `commit_secondaries` writes each other key's record and deletes its lock if it is still the
  transaction's, in the buffer's order (any order here). The guard is dropped at the return,
  and once the commit or its rollback is done `commit` unregisters from `ActiveTxnRegistry`.
- `rollback` unregisters the writer from `InflightWriteRegistry` and, for each buffered key whose
  lock is its own, deletes the lock, deletes the data at `start_ts`, then writes a Rollback record
  at `start_ts`. `Drop` of a transaction not committed calls `rollback`, then unregisters it.
- External-apply mode (`set_external_apply`): the embedder registers each writer in flight at its
  first write (`InflightWriteRegistry::register`: the insert, then the `insert_epoch` fetch-add),
  commit leaves it registered, and the embedder unregisters it with `mark_txn_applied` after its
  own apply. A process of its own calls `safe_read_ts(oracle_now)` with a fresh `oracle_now`.
  `min_ts` loads the epoch, walks the registry, loads the epoch again, and merges an unstable pass
  into the least value seen, answering that after `SCAN_RETRIES` passes. `safe_read_ts` answers
  `oracle_now` when no writer is at or below it, spins and calls `min_ts` again below the cap, and
  past it answers `min(oracle_now, m.saturating_sub(1))`.
- Garbage collection: the crate never calls `gc_writes` or `gc_data` itself. A process of its own
  runs them as an embedder would, for each key or passing one over, with the watermark from
  `KovanMVCC::gc_watermark` (`Watermark = "registry"`: `issued` loaded as a bound, then the walk
  of `ActiveTxnRegistry`, the least of the two) or with any watermark at or below every timestamp
  a live transaction reads at (`"sound"`, an embedder that computes it right). `gc_writes` keeps
  the latest Put or Delete at or below the watermark and every record above it; `gc_data` keeps
  the data that commit names and every version above it.

Every call into a `kovan_map` map is one step: `HashMap` for the locks, for the outer maps of the
records and the data, and for `ActiveTxnRegistry`; `HopscotchMap` for `InflightWriteRegistry`.
The [chained](../chained/README.md) and [hopscotch](../hopscotch/README.md) families prove each of
these calls linearizable. A walk of a map (`min_active_ts`, `min_ts`) is two steps, its start and
its end, and yields every entry present for its whole length and any of those present at some
moment of it, which is what the two families' `WalkExact` proves. Each version-chain call
(`put_write`, `get_latest_write`, `get_latest_commit`, `put_data`, `get_data`, `delete_data`,
`gc_writes`, `gc_data`) is one step, its critical section under the key's `parking_lot` mutex.
The outer map's entry for a key is made once (`insert_if_absent`; the loser takes the winner's)
and never removed, so a lookup that finds no entry is one that finds an empty chain. A record is
`[ts, st, kind]`, and a `BTreeMap` insert at a timestamp already there replaces it.

What is left out or folded, and why it changes nothing:

- Memory orderings. The model is sequentially consistent, as every model here. kovan-mvcc's own
  atomics are the oracle's `SeqCst` fetch-add and the epoch's `Release` fetch-add and `Acquire`
  loads; everything else goes through `kovan_map`, whose families and tests cover its orderings,
  and `parking_lot` mutexes. Nothing in the workspace checks kovan-mvcc's own orderings: CI's
  Miri run (`.github/workflows/miri.sh`) covers the `kovan` crate only, and the crate's one
  shuttle test, `tests/shuttle_lock_table.rs`, races `LockTable::try_lock`, whose
  `insert_if_absent` logic `put_lock` copies. The native tests (`tests/concurrent_stress.rs`,
  `tests/stress_bank.rs`, `tests/minimal_bank.rs` and the others) run the protocol on threads.
- The backoff's count is folded: a read that meets a lock may look again or give up at any look.
  The code gives up at its ninth look (`DefaultBackoff`; the Lean proof checks the schedule), and
  every behaviour of the code is one of the model's: a give-up at an earlier look is the code's
  ninth look with the looks between, steps of the reader alone that change nothing, taken in a
  row. The model has more behaviours (a read that waits longer), so a passing check covers the
  code, and every `BackoffStrategy` an embedder installs with `set_backoff`.
- `SPIN_CAP` (40) and `SCAN_RETRIES` (64) are 1 and 2 here. A spin and an unstable pass only read
  shared state, so the code's further spins and passes, taken in a row with nothing else moving,
  end as the model's last one does; a cap the model reaches sooner than the code only adds
  behaviours. `safe_read_ts`'s PAUSE loop is its own thread's work.
- Timestamps are counted without wrapping. The Lean proof (`proofs/lean/Kovan/Mvcc.lean`) shows
  the oracle answers `c + k + 1`, increasing, until the counter reaches `u64::MAX`, and what comes
  after.
- Transaction ids (`Uuid::new_v4().as_u128()`) are the process ids: distinct, as two random
  122-bit ids are but for a chance the model does not take. `short_value` is always `None` in the
  code. `LockInfo::primary_key` is never read by anything in the crate (no transaction resolves
  another's lock), so the model leaves it out.
- A read finding its own lock (`percolator.rs:540`) and `put_lock` finding its own lock
  (`storage.rs:124`) are unreachable: `commit` consumes the `Txn`, so no read follows a prewrite,
  and pass 1 locks each key once. Both are transcribed and never taken. `commit_primary`'s
  `PrimaryLockMissing` and `PrimaryLockMismatch` are unreachable too, since no thread deletes a
  lock that is not its own (`PrimaryHeld` checks it).
- After a failed prewrite, `rollback`'s `get_lock` of each key finds no lock of its own (the
  prewrite released each one it took), and after a drop none was taken: those loads change
  nothing and are left out. A registry's `register` and `unregister` steps are left out where no
  thread reads that registry (no GC, no `safe_read_ts` caller), and outside external-apply mode
  `inflight_writes.unregister` removes an entry no one made.
- Not modelled: `min_active_ts_bounded`, which leaves transactions older than `max_age` out of
  the watermark on purpose (their reads are not protected); `len` and `is_empty`; the walk of
  `scan_write_keys` (the GC takes each key or passes it over, which covers any subset a walk
  yields); `MockTimestampOracle::set`, a test hook that can move the counter back; `Storage`
  implementations other than `InMemoryStorage`; an embedder that registers writers outside
  external-apply mode. Each transaction's operations run in program order on one thread.

## Properties

Every check made at the step it is about is recorded in `errs`; each of these invariants says one
kind of check never failed.

- `TsIncreasing`: every timestamp the oracle hands out is greater than every one it handed out
  before, so no two are equal.
- `SnapshotRead`: a read that answers from the version chain answers the value of the latest
  version committed at or before its read timestamp (`start_ts`, or ReadCommitted's fresh one),
  None for a Delete or no version. The latest version is that of the transaction with the
  greatest `commit_ts` at or below the read timestamp among those that wrote the key; each such
  transaction took its `commit_ts` before the read took its timestamp, and in the code every
  transaction that takes one commits.
- `NoDirtyRead`: no read answers a value whose transaction had not committed at or before the
  read's timestamp.
- `VersionData`: the version a read finds still has its data.
- `GiveUpSound`: a read that gives up answers no value: `Err(LockConflict)`, never a None the
  snapshot may contradict.
- `SerialReads`: a Serializable transaction that takes its `commit_ts` read no key another
  Serializable transaction committed after its `start_ts`. With the snapshot reads of the
  read-only Serializable transactions (which validate nothing: `commit` returns before the
  validation when nothing was written), this makes the Serializable transactions serializable in
  timestamp order.
- `WatermarkSound`: a GC watermark from `gc_watermark` is at or below every timestamp a live
  transaction (begun, not yet committing or dropped) reads at.
- `SafeReadTs`: `safe_read_ts` never answers a horizon at or above the `commit_ts` of a writer
  whose external apply has not finished (`mark_txn_applied` has not returned).
- `FirstCommitterWins`: two transactions that overlap in time (each `start_ts` below the other's
  `commit_ts`) and write a common key do not both commit (write their primary's record).
- `PrimaryDecides`: a secondary's commit record exists only once its primary's does.
- `AllOrNothing`: a finished transaction committed every key it wrote, or none, and it committed
  exactly when it took a `commit_ts`.
- `PrimaryHeld`: `commit_primary` always finds the primary's lock its own.
- `NoLeak`: when every thread is done, no lock is left, no data of a transaction that did not
  commit, both registries are empty and the SSI lock is free. Records stay, Rollback records too:
  the crate never collects them itself.
- `Termination` (under `FairSpec`, every thread's steps taken fairly): every transaction, GC pass
  and `safe_read_ts` call ends. `LocksReleased` (the same): every lock is released.
- `ReadersEnd` (under `ReadersSpec`: only the read-only transactions and the `safe_read_ts`
  caller are scheduled fairly, and a writer may stop anywhere, holding its locks or its
  registration): every reader and every `safe_read_ts` call ends, as the code documents. A read
  backs off and gives up; `safe_read_ts` pins below a writer past its cap.

## What TLC found, and the fixes

TLC broke six properties on the code before this fix, each now a passing configuration with the
old rule kept as a mutation that breaks it again (`kovan-mvcc/tests/model_findings.rs` has a test
for each that fails on the old rule):

- The give-up (`MV_give_up`; `giveup_answers_none`, `GiveUpSound`): a read that kept meeting a
  lock gave up and answered None, the answer for a key that holds no value, though the lock's
  holder could commit into the read's snapshot. `read` now returns
  `Result<Option<Vec<u8>>, MvccError>` and answers `Err(LockConflict)`; the backoff strategy the
  caller sets decides how long it waits.
- The SSI validation (`MV_ssi_rollback`; `ssi_latest_record`, `SerialReads`): it read each key's
  latest record, and a Rollback record above a commit hid the commit, letting two Serializable
  transactions that each read what the other wrote both commit. It reads the latest commit now
  (`get_latest_commit`); the Lean proof's `ssiFails_exact` shows that check exact.
- `gc_writes` (`MV_gc_rollback`; `gc_keeps_latest_record`, `SnapshotRead`): it kept the latest
  record at or below the watermark, of any kind, so a kept Rollback record took the commit under
  it. It keeps the latest commit now (Lean: `gcWrites_keeps_reads`, `gcWrites_keeps_prewrite`).
- `gc_data` (`MV_gc_data`; `gc_keeps_latest_data`, `VersionData`): it kept the latest data at or
  below the watermark, so a prewrite not yet committed took the committed version's data under it.
  It keeps the data the latest commit names now (Lean: `gcData_keeps_reads`).
- The watermark (`MV_watermark`, `MV_watermark_read`; `register_after_ts` and `walk_only`,
  `WatermarkSound`): `begin` took `start_ts` and only then registered, and `min_active_ts`'s walk
  may miss an entry inserted during it, so a GC could take a later transaction's `start_ts` as the
  watermark and collect versions an earlier one reads. Now `begin` registers first, under a bound
  at most its `start_ts`, and `gc_watermark` bounds the walk by `issued` loaded before it: a
  transaction the walk misses registered after it began, and its `start_ts` is above the bound.
- The unregister order (`MV_inert_unregister_first`, expected to pass): `commit` unregistered at
  its start and `Drop` before its rollback, so a watermark could pass a prewrite. With the GC
  passes fixed no property tells the two orders apart; they unregister at the end now all the same,
  as `gc_watermark`'s doc promises.

Where the code and its docs disagreed, now fixed: `lib.rs` says which isolation level gives
snapshot isolation (`begin()` gives ReadCommitted); `InflightWriteRegistry::register` keeps the
first `start_ts`, as its doc says (`insert_if_absent`); `set_external_apply`'s doc names
`mark_txn_applied`, and the `inflight_writes` field's says the embedder registers. Left as they are:
the epoch validation of `min_ts`, whose comment gives a relocation as its reason where
`HopscotchMap::iter`'s contract (which the hopscotch family checks) already yields an entry present
for the whole walk (`MV_inert_epoch_ignored` passes: it is harmless); `LockTable`, exported as the
lock manager but unused by the protocol, which takes its locks with `InMemoryStorage::put_lock`;
and `LockInfo::primary_key`, which nothing reads.

## Mutations and witnesses

Each mutation puts back one wrong rule and lists its property first, the others after it, so that
TLC, which stops at the first state that breaks any of them, names the one the mutation is for.
`lock_get_then_insert` is checked against `FirstCommitterWins` and, in a second configuration,
against `PrimaryHeld` alone. The liveness mutations check their temporal property alone.
The six that put back the code before the fixes are named in the section above.

| configuration | the wrong rule | expected |
|---|---|---|
| `MV_mut_oracle_load_store` | `get_timestamp` as a load and a store of the counter, at begin | `TsIncreasing` broken |
| `MV_mut_read_ignores_lock` | a read goes to the write column without loading the key's lock | `SnapshotRead` broken |
| `MV_mut_read_data_column` | a read answers the latest data at or below its timestamp, without the write column | `NoDirtyRead` broken |
| `MV_mut_rollback_deletes_range` | rollback's `delete_data` drops every version at or below its `start_ts` | `VersionData` broken |
| `MV_mut_skip_newer_commit` | pass 2 rejects a Rollback record only, not a commit at or after `start_ts` | `FirstCommitterWins` broken |
| `MV_mut_check_before_lock` | pass 2 runs before pass 1 | `FirstCommitterWins` broken |
| `MV_mut_lock_get_then_insert` | `put_lock` as a get, then an insert | `FirstCommitterWins` broken |
| `MV_mut_lock_get_then_insert_primary` | the same | `PrimaryHeld` broken |
| `MV_mut_secondaries_first` | commit writes the secondaries' records before the primary's | `PrimaryDecides` broken |
| `MV_mut_validate_after_primary` | the SSI validation runs after the primary committed | `AllOrNothing` broken |
| `MV_mut_no_ssi_lock` | Serializable transactions validate and commit without `ssi_commit_lock` | `SerialReads` broken |
| `MV_mut_rollback_keeps_data` | rollback leaves the data at `start_ts` | `NoLeak` broken |
| `MV_mut_ext_commit_unregisters` | commit unregisters the writer in external-apply mode too | `SafeReadTs` broken |
| `MV_mut_cap_returns_now` | past the spin cap `safe_read_ts` answers `oracle_now` | `SafeReadTs` broken |
| `MV_mut_ssi_lock_kept` | a failed validation returns without dropping the SSI guard | `Termination` broken |
| `MV_mut_secondary_keeps_lock` | `commit_secondaries` writes the record and leaves the lock | `LocksReleased` broken |
| `MV_mut_read_waits` | a read that meets a lock looks again until it is gone, never giving up | `ReadersEnd` broken |
| `MV_mut_spin_unbounded` | `safe_read_ts` spins with no cap while a writer is at or below `oracle_now` | `ReadersEnd` broken |
| `MV_mut_giveup_answers_none` | a read whose backoff gives up answers None | `GiveUpSound` broken |
| `MV_mut_ssi_latest_record` | the SSI validation reads each key's latest record, a Rollback record too | `SerialReads` broken |
| `MV_mut_gc_keeps_latest_record` | `gc_writes` keeps the latest record of any kind | `SnapshotRead` broken |
| `MV_mut_gc_keeps_latest_data` | `gc_data` keeps the latest data of any kind | `VersionData` broken |
| `MV_mut_register_after_ts` | `begin` takes `start_ts`, then registers it | `WatermarkSound` broken |
| `MV_mut_walk_only` | the watermark is `min_active_ts`'s walk alone, with no bound | `WatermarkSound` broken |

Not every plausible wrong rule has an effect any thread can see, and three have configurations of
their own, expected to pass (`MV_inert_*`, not the code). Writing the secondaries' records first
breaks only `PrimaryDecides`: a reader waits on each key's own lock, and nothing in the crate reads
a primary to decide a secondary, so no read tells the two orders apart
(`MV_inert_secondaries_first`, every other safety property at `MV_si`'s size). The epoch of
`min_ts` bumped before the insert, with every pass trusted without its second load, breaks nothing
either (`MV_inert_epoch_ignored`), for the reason above; nor does unregistering at the start of
`commit` (`MV_inert_unregister_first`), now that both GC passes keep what a read needs.

The witnesses each claim a case never happens, so their counterexamples show the passing
configurations reach it: a read finds a lock of a transaction that started before it
(`MV_wit_sight`, `NoSightW`) and one whose primary already committed (`MV_wit_half_read`,
`NoHalfReadW`); a read meets a version older than the key's latest commit (`MV_wit_old_version`,
`NoOldVersionW`), and a ReadCommitted read one committed after its transaction began
(`MV_wit_fresh_rc`, `NoFreshRcW`); a prewrite finds another lock (`MV_wit_lock_conflict`,
`NoLockConflictW`), a commit at or after its start (`MV_wit_write_conflict`, `NoWriteConflictW`)
and a Rollback record at or after it (`MV_wit_rollback_reject`, `NoRollbackRejectW`); an SSI
validation fails (`MV_wit_ssi_fail`, `NoSsiFailW`); a primary commits while a secondary is still
locked (`MV_wit_half_commit`, `NoHalfCommitW`); `safe_read_ts` pins below `oracle_now`
(`MV_wit_pin`, `NoPinW`), answers `oracle_now` after spinning (`MV_wit_drain`, `NoDrainW`), and a
`min_ts` pass sees the epoch move (`MV_wit_unstable`, `NoUnstableW`).

## Configurations

Each transaction's program is its isolation level (RR Repeatable Read, RC ReadCommitted, SER
Serializable), its operations (`r1` reads key 1, `w1` writes it, `d1` deletes it) and its end, a
commit unless marked drop. The configurations with a `safe_read_ts` caller run in external-apply
mode with `SPIN_CAP` 1 and `SCAN_RETRIES` 2.

| configuration | transactions | other threads | seeded | checks |
|---|---|---|---|---|
| `MV_si` | RR `w1 w2`; RR `w2 w1`; RR `r1 r2`; RR `r2 r1` | | 1 | the safety properties but `GiveUpSound`, `WatermarkSound`, `SafeReadTs` |
| `MV_rc` | RR `w1 w2`; RC `r1 r2 r1`; RR `d1 w2 d2` | | 1, 2 | the same |
| `MV_rw` | RR `r1 w1 r1`; RR `r1 w1`; RR `w2 w1`, drop; RC `r1 r2 w2` | | 1 | the same |
| `MV_ser` | SER `r1 w2`; SER `r2 w1`; RR `r1 r2 w1`; SER `r2 r1` | | 1, 2 | the same |
| `MV_ext` | RR `w1`; RR `w2 w1`; RR `w2`, drop | `safe_read_ts`, one call | 1 | the same and `SafeReadTs` |
| `MV_live` | RR `w1 w2`; SER `r1 w2`; RC `r2` | | 1, 2 | `MV_si`'s; `Termination`, `LocksReleased` under `FairSpec` |
| `MV_live_ext` | RR `w1`; RR `w2 w1` | `safe_read_ts`, one call | 1 | `MV_ext`'s; `Termination`, `LocksReleased` under `FairSpec` |
| `MV_live_readers` | RR `w2 w1`; RR `r1 r2` | `safe_read_ts`, one call | 1 | `MV_ext`'s; `ReadersEnd` under `ReadersSpec` |
| `MV_inert_secondaries_first` | `MV_si`'s, with `secondaries_first` | | 1 | `MV_si`'s but `PrimaryDecides` |
| `MV_inert_epoch_ignored` | RR `w1`; RR `w2 w1`, with `epoch_ignored` | `safe_read_ts`, two calls | 1 | `MV_ext`'s |
| `MV_give_up` | RR `w1`; RR `r1` | | 1 | the read properties, `GiveUpSound` among them |
| `MV_ssi_rollback` | SER `r1 w2`; SER `r2 w1`; SER `r3 w1`; RR `w3` | | none | the same, `SerialReads` among them |
| `MV_gc_rollback` | SER `r2 w1`; RR `w2`; RR `r1` | GC, a sound watermark, one pass | 1 | the same |
| `MV_gc_data` | RR `w1`; RR `r1` | GC, a sound watermark, one pass | 1 | the same |
| `MV_watermark` | RR `r1`; RR `r1` | GC, `gc_watermark`, one pass | 1 | the same |
| `MV_watermark_read` | RR `r1`; RR `r1`; RR `w1` | GC, `gc_watermark`, one pass | 1 | the same |
| `MV_inert_unregister_first` | `MV_gc_data`'s, with `unregister_first` | GC, a sound watermark, one pass | 1 | the same |

The mutations and witnesses run on smaller programs, so their traces stay short: RR `w1 w2`, RR
`w2 w1` and RR `r1 r2` (key 1 seeded) for most; `MV_ser`'s first three transactions for
`no_ssi_lock`, `rollback_keeps_data`, `rollback_deletes_range` and two witnesses; `MV_live_ext`'s
for `ext_commit_unregisters`, `cap_returns_now` and the external witnesses; `MV_live_readers`' for `read_waits` and `spin_unbounded`; SER `r1 w2 w3` and RR `w1`
for `validate_after_primary`; SER `r1 w2`, RR `w1` and SER `w3` for `ssi_lock_kept`; RR `w1 w2`
and RR `r2` for `secondary_keeps_lock`. The six mutations of the fixes run the programs of the six
configurations above they guard. `MV_inert_secondaries_first` reaches exactly as many states
as `MV_si`; the same rule breaks `PrimaryDecides` in `MV_mut_secondaries_first`, so it is in
effect.

## Code map

| label | function | code | step |
|---|---|---|---|
| `BG0` | `begin_with_isolation`, `ActiveTxnRegistry::register` | `percolator.rs:414-417`, `:23-25` | the registry's insert under `issued` |
| `BG1` | `begin_with_isolation`, `take_timestamp`, `get_timestamp` | `percolator.rs:418`, `:12-16`, `timestamp_oracle.rs:41-44` | `start_ts`, the counter's fetch-add, `issued`'s fetch-max |
| `BG1b` | (`oracle_load_store`) | | the store of the value loaded |
| `BG2` | `ActiveTxnRegistry::register` | `percolator.rs:419`, `:23-25` | the entry's value replaced by `start_ts` |
| `OP` | `write`, `delete`, `read` | `percolator.rs:622-639`, `:459-482` | the thread's own work: the buffer, a read of a buffered key, a Repeatable Read or Serializable `read_ts` |
| `XR1`, `XR2` | `InflightWriteRegistry::register` (the embedder) | `percolator.rs:131-137` | the insert, then the epoch's fetch-add |
| `RO` | `read`, `get_timestamp` | `percolator.rs:529` | ReadCommitted's `read_ts` |
| `RL` | `read`, `get_lock`, `DefaultBackoff::backoff` | `percolator.rs:533-575`, `storage.rs:116-118`, `backoff.rs:38-54` | the lock loaded; look again, or give up: `Err(LockConflict)` |
| `RW` | `read`, `get_latest_commit` | `percolator.rs:578-606`, `storage.rs:170-182` | the latest Put or Delete at or before `read_ts` |
| `RD` | `read`, `get_data` | `percolator.rs:589-618`, `storage.rs:199-206` | the data at the record's `start_ts`, or None |
| `DR1`, `DR2` | `Drop`, `rollback` | `percolator.rs:878-886`, `:854` | the in-flight registry's removal (`rollback`), then the active one's |
| `CM0` | `commit`, `commit_registered` | `percolator.rs:641-653` | `committed`, a read-only commit's return |
| `PL`, `PL2` | `prewrite` pass 1, `put_lock` | `percolator.rs:749-758`, `storage.rs:120-136` | the lock's `insert_if_absent` |
| `PF` | `prewrite` | `percolator.rs:752-754`, `:706-708`, `:713-715` | a lock taken released, in the order taken |
| `RBP` | `commit`, `rollback` | `percolator.rs:662-665`, `:796` | the in-flight registry's removal after a failed prewrite |
| `PC` | `prewrite` pass 2, `get_latest_write` | `percolator.rs:761-782`, `storage.rs:158-167` | the latest record against `start_ts` |
| `PD` | `prewrite` pass 3, `put_data` | `percolator.rs:785-789`, `storage.rs:184-197` | the data at `start_ts` |
| `SL` | `commit` | `percolator.rs:669-673` | `ssi_commit_lock` taken |
| `SV` | `commit`, `get_latest_commit` | `percolator.rs:675-692` | a read-set key's latest commit |
| `CT` | `commit`, `take_timestamp` | `percolator.rs:699` | `commit_ts`, `issued`'s fetch-max |
| `CP1` | `commit_primary`, `get_lock` | `percolator.rs:795-804` | the primary's lock, its own |
| `CP2` | `commit_primary`, `put_write` | `percolator.rs:807-817`, `storage.rs:142-155` | the primary's record: the commit |
| `CP3` | `commit_primary`, `delete_lock` | `percolator.rs:820`, `storage.rs:138-140` | the primary's lock deleted |
| `CS1`, `CS2`, `CS3` | `commit_secondaries` | `percolator.rs:826-851` | a secondary's record, its lock loaded, deleted when its own |
| `CE` | `commit` | `percolator.rs:714-718` | the removal outside external-apply mode, the guard dropped |
| `UR`, `URX` | `commit` | `percolator.rs:643-646` | the active registry's removal, once the commit or its rollback is done |
| `XA` | `mark_txn_applied` (the embedder) | `percolator.rs:319-321`, `:127-129` | the in-flight registry's removal after the apply |
| `RB0` | `commit`, `rollback` | `percolator.rs:704`, `:796` | the in-flight registry's removal |
| `RB1`-`RB4` | `rollback`, `get_lock`, `delete_lock`, `delete_data`, `put_write` | `percolator.rs:857-874`, `storage.rs:208-213` | the lock loaded; then the lock, the data, the Rollback record |
| `HZ0` | `safe_read_ts` (the embedder's `oracle_now`) | `percolator.rs:339-352` | `oracle_now` from the oracle |
| `HZ1`-`HZ3` | `min_ts` | `percolator.rs:152-164` | the epoch loaded; the walk's start and end |
| `HZ4` | `min_ts`, `safe_read_ts` | `percolator.rs:165-175`, `:333-353` | the epoch again, the merge; the answer, or a spin |
| `GC0`, `GC1` | `gc_watermark`, `min_active_ts` | `percolator.rs:385-390`, `:47-57` | `issued` loaded, the walk's start and end, the least of the two |
| `GC2`, `GC3` | `gc_writes`, `gc_data`, `latest_commit_at_or_below`, `remove_below` | `storage.rs:215-245`, `:71-84` | one key's collection |

## TLC results

The run recorded in `tlc-run.txt` (4 workers for a passing configuration, one for a violation,
at the lowest priority on a 36-core machine shared with other heavy work): 53 of 53
configurations match `EXPECTED.txt`, in 511 s of TLC time. The largest passing ones are `MV_ext`
(7,127,582 distinct states, 78 s), `MV_ssi_rollback` (3,422,064, 38 s), `MV_ser` (2,691,886, 38 s),
`MV_rw` (2,347,872, 30 s) and `MV_gc_rollback` (1,021,644, 13 s). The longest run that breaks a
property is `MV_mut_ssi_latest_record` (3,280,327 distinct states, 123 s, on one worker): the
trace of the masked validation needs four transactions.
