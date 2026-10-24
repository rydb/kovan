# The software transactional memory (`Stm.tla`)

One family of [kovan's TLA+ models](../README.md), which says how to run them.

## What is transcribed from the code

`kovan_stm` (`kovan-stm/src/lib.rs`, `transaction.rs`, `var.rs`, `node.rs`) at the grain of its
atomic steps: the version clock, each variable's version lock word and node pointer, its reference
count, the transactions' read and write sets, and kovan's reclamation of the nodes the commits and
the variables' drops retire.

- `atomically` pins a guard for each attempt and `Transaction::new` loads the clock: the read
  version. The closure's operations run in order: a store buffers a fresh value in the write set
  (a second store to the variable drops the first one's value), a load of a variable the
  transaction wrote answers that value, a load of a variable it read before loads the node pointer
  again and clones its value with no version check, and any other load reads the lock word (locked,
  or a version newer than the read version: `Retry`), the pointer, the lock word again (changed or
  locked: `Retry`), records the read entry and clones the value. The closure may return
  `Err(Retry)`, and may drop its handle of a variable (`Option::take`), after which it skips the
  variable.
- A read-only commit marks the transaction committed and runs its commit hooks, with no
  validation. Otherwise the commit locks its write set in address order (the lock word loaded,
  then its compare-and-swap; a lock held by another committer aborts, releasing the locks taken; a
  variable read and written since aborts, releasing this lock and those before it), takes the
  write version with the clock's fetch-add, loads the lock word of each read entry it did not write
  (locked, or newer than read: abort, releasing every lock), then publishes each write
  (`Write::commit`: a fresh node swapped in, the replaced node retired, the version stored, the
  entry's reference to the variable dropped), and returns, running its commit hooks.
- The end of an attempt drops the transaction: the values its write set still holds, every entry's
  reference, the rollback hooks unless it is marked committed; then the guard. A variable whose last
  reference (a handle, a read entry, a write entry) goes is dropped: `TVarInner::drop` retires its
  node and the reference count frees the rest.
- kovan's reclamation is what [the reclamation family](../reclaim/README.md) proves of it: a
  retired node is freed, its value dropped, once every guard that was pinned when it was retired
  has dropped.

Each thread runs a program (`MC_Stm.tla`): a sequence of transactions, each a sequence of
operations. A thread holds a handle of every variable its program names and drops those it still
holds when its program ends. Every value is its own token, so every read is traced to the commit
that wrote it.

What is left out or folded, and why it changes nothing:

- The version clock and every version are kept as their ranks among the numbers in use: the
  clock's fetch-add takes the next number and renames every number held (the clock, the versions,
  the read versions, the read entries, the words and write versions in hand) to its rank. Every
  decision of the protocol compares two of these numbers, and the renaming keeps every comparison,
  so the clock never grows out of the state space, also in a run where transactions abort forever.
  The lock word is a pair (a lock bit and a version). `proofs/lean/Kovan/Stm.lean` proves the
  code's packing of the two into one `u64` (`val & 1`, `val & !1`, `current | 1`, `fetch_and(!1)`,
  the store of an even version) decides the same, that the clock moved by 2 stays even and does not
  wrap before `2^63` fetch-adds, that a version is newer than a read version exactly when its
  commit's fetch-add came after the read version's load, and that renaming to ranks keeps every
  `<` and `=` between numbers in use.
- A thread's private work between two shared steps is folded into the shared step next to it,
  which no other thread can tell apart: the stores, the loads a write set answers, the
  dispatch of the closure's operations, the read entry's insertion, the decisions on a word loaded.
  The end of an attempt (the transaction's drop and the guard's drop) is folded into the step that
  decided the abort; after a commit it is its own step, which also runs the commit hooks.
- The pin and the clock's load are one step: a node retired between the two is unlinked before it
  is retired, so it is not one this attempt loads, and whether the attempt counts as its holder
  changes nothing but when kovan frees it.
- A reference count's increments and decrements commute with every other step but the decrement
  that reaches zero, which runs the variable's drop: the model counts the references (handles,
  read entries, write entries) and drops the variable in the step that releases the last one. The
  drop's own pin, its load of the pointer (no other thread can write it any more) and its retire
  are one step. The `TVar` handle is one reference however many threads share it (behind an `Arc`,
  or borrowed in a scope): the model gives each thread that names a variable a reference of its
  own, which drops the variable at the same moment, when the last one goes.
- `Write::commit`'s swap and its retire of the replaced node are one step: the swap unlinked the
  node, so no load reaches it after, and a thread that pins in between is not one that can hold it.
  The node's allocation and the nested pin are private.
- `compare_exchange_weak`'s spurious failure returns the word as it is and the loop tries again: a
  step that changes nothing shared, left out.
- Variables are numbered in the order of their addresses, the order a commit locks them in (the
  write set is a `BTreeMap` keyed by the address of the variable's inner allocation).
- Under the `recycle` feature a node's memory comes from kovan's magazine cache and goes back to
  it when kovan frees the node; the STM sees an allocation and a free either way, and the cache is
  [the magazine family](../magazine/README.md) and [the slab family](../slab/README.md).
- The closure's values are tokens: a store's value does not depend on what the transaction read.
  Every property here is about which values each transaction read and wrote, which tokens trace
  exactly.
- A closure that returns `StmError::User` panics out of `atomically`; the unwinding drops the
  transaction as an abort does. Not modelled: the thread ends there.
- The hooks are the code's flag (`committed`) and the order of the steps that run them: every
  transaction has a commit hook and a rollback hook, and running them is an event.
- A variable created inside a closure is a new variable at each attempt. The model's variables
  exist from the start; a variable whose last handle the closure drops (`<<"d", x>>`) covers the
  same paths: the read entry or the write entry is its last reference, dropped at the attempt's end
  or by the commit itself.
- Memory orderings: the model is sequentially consistent, as every model here. Miri in CI
  (`.github/workflows/miri.sh`) runs `kovan-stm/tests/reread.rs` and `tests/drops.rs`, so the
  orderings of a load racing a commit, and of a commit's drops, are checked on those programs and
  no others; the shuttle suite (`kovan-stm/tests/shuttle_stm.rs`, run by
  `.github/workflows/shuttle-test.sh`) explores schedules with sequentially consistent atomics. The
  argument the code rests on, not checked: a load's pointer load is `Acquire`, so its second lock
  word load cannot move before it, and a pointer it reads from a commit's `AcqRel` swap makes the
  commit's earlier lock compare-and-swap visible to that second load; the clock's `AcqRel`
  fetch-adds are one modification order, so of two commits the later one's validation loads see
  every lock the earlier one took before its fetch-add.

## Properties

Every check is made at the step it is about and recorded in `errs`; each invariant says one kind
of check never failed.

- `Serializable`: the committed transactions are serializable, in an order that keeps real time.
  At each commit the model builds their dependencies: a transaction depends on another whose write
  it read, whose write it overwrote, which read a value it overwrote (each variable's values in the
  order the commits decided them), or which returned before it began. The dependencies must form
  no cycle.
- `Opacity`: every attempt, committed, running or aborted, reads a state the committed
  transactions can be serialized around: at each of its reads and at every commit while it runs,
  the attempt placed among the committed transactions as a read-only one (after those whose writes
  it read and those that returned before it began, before those that overwrote what it read)
  closes no cycle. Each attempt is checked on its own; the model does not check that one order
  serves every aborted attempt at once.
- `AllOrNone`: no attempt sees one write of a committed transaction and, for another variable
  that transaction wrote, a value older than its write.
- `DropOnce`: no value is dropped twice, and no node retired twice.
- `NoUseAfterFree`: no clone reads a node kovan freed or a value already dropped, and no step
  touches a variable's lock word or pointer after the variable was freed.
- `NoLeak`: once every thread and the reclamation are done, every variable was freed, every node
  freed, and every value made dropped exactly once; and no value was made again (by a new attempt)
  before its earlier making was dropped.
- `LockOwned`: a variable's lock bit is set exactly while one committer holds it.
- `HooksRight`: the rollback hooks never run for a transaction that committed, and the commit
  hooks run after every lock is released.
- `Termination` (under `FairSpec`, every thread and the reclamation scheduled fairly): every
  thread finishes, in the configurations where no two transactions each read what the other
  writes. `SoloEnds` (under `FairSpec`): once every other thread is done, a thread finishes, so a
  transaction running alone commits. The code claims no more: two transactions that each read
  what the other writes can abort each other forever under a fair schedule (`ST_wit_livelock`).

## What TLC found, and the fix

**A transaction that loaded a variable twice could see two values of it, and a read-only one
committed so.** Before f691cc5, `Transaction::load` answered a load of a variable already in the
read set by loading the node pointer again and cloning its value, with no look at the lock word
(its comment said "We already validated this version, re-read raw just to get value", but the node
it loaded could be newer than the version it validated), and a read-only transaction commits
without validating. The minimal case: thread 1 loads x (the initial value, version 0); thread 2
locks x, takes the write version and swaps its node in; thread 1 loads x again, from the read set,
and gets thread 2's value while x is still locked; it commits, read-only, having read x as 0 and as
1. The same path broke `Opacity` for an update transaction, which saw both values before its
commit's validation aborted it, and `AllOrNone` for a transaction that loaded x, then y, then x
again while a commit wrote both. A program against the crate showed the first case: a read-only
`atomically` that loads a `TVar` twice around another thread's commit of it returned `(0, 1)`.

Now every load takes the validated path, a repeat one too, and a repeat load must find the version
its first load recorded (`transaction.rs:190-224`). The three cases pass (`ST_reread`,
`ST_reread_update`, `ST_reread_torn`), the old shortcut is the mutation `reread_unvalidated`, and
`kovan-stm/tests/reread.rs` fails on the old code with `(0, 1)`. The check of the first load's
version never fires (`ST_reread_stable`): a commit's write version is above the read version of
every transaction already running, so a variable written since the first load is caught by the
check against the read version before it.

## Mutations and witnesses

Each mutation puts back one wrong rule and lists its property first, the others after it, so
that TLC, which stops at the first state that breaks any of them, names the one the mutation is
for. The first five put back four defects this crate had (`keep_locks` twice: its safety
property, then its liveness one), and the last three the fifth.

| configuration | the wrong rule | expected |
|---|---|---|
| `ST_mut_commit_copies_value` | the code before 01d8a16: the commit publishes a bitwise copy of the value, and the write entry, still owning it, drops it too | `DropOnce` broken |
| `ST_mut_keep_locks` | the code before 0f88841: a commit that meets a lock held by another committer aborts without releasing the locks it took | `LockOwned` broken |
| `ST_mut_keep_locks_live` | the same, scheduled fairly: the transaction that kept the lock retries on it forever | `Termination` broken |
| `ST_mut_no_var_retire` | the code before 7d0c6fe: a variable has no drop, so its last node is never retired | `NoLeak` broken |
| `ST_mut_no_keep_alive` | the code before 7d0c6fe: a read entry keeps a raw pointer to the variable and no reference, so a variable whose handle the closure dropped is freed before the commit validates it | `NoUseAfterFree` broken |
| `ST_mut_free_now` | the commit frees the node it replaces at once instead of retiring it | `NoUseAfterFree` broken |
| `ST_mut_skip_read_validation` | an update transaction's commit skips the read-set validation, as a read-only one does | `Serializable` broken |
| `ST_mut_no_rv_check` | a load accepts a version newer than the read version, checking only the lock bit | `Opacity` broken |
| `ST_mut_version_before_swap` | the commit stores the version (releasing the lock) before swapping the new node in | `AllOrNone` broken |
| `ST_mut_read_only_not_committed` | the read-only commit does not mark the transaction committed, so its drop runs the rollback hooks | `HooksRight` broken |
| `ST_mut_stale_read_version` | a new attempt keeps its transaction's first read version instead of loading the clock again | `SoloEnds` broken |
| `ST_mut_reread_unvalidated` | the code before f691cc5: a load of a variable already read loads the pointer again with no look at the lock word, for a read-only transaction (`Opacity` and `AllOrNone`, which the attempt breaks first, left out) | `Serializable` broken |
| `ST_mut_reread_unvalidated_update` | the same, for an update transaction that sees both values before it aborts | `Opacity` broken |
| `ST_mut_reread_unvalidated_torn` | the same, for a transaction that sees x new and y old | `AllOrNone` broken |

The witnesses each claim a case never happens, so their counterexamples show the passing
configurations reach it: a commit aborts on a lock another holds (`ST_wit_lock_abort`), on a
variable it read and another commit wrote since (`ST_wit_version_abort`), and at its read-set
validation (`ST_wit_validate_abort`); a load retries at its first look at the lock word
(`ST_wit_read_retry`) and at its second (`ST_wit_post_retry`); a repeat load finds the version its
first recorded and is answered (`ST_wit_reread`), or retries (`ST_wit_reread_retry`); a variable's last reference is a transaction's entry, dropped at the attempt's
end (`ST_wit_entry_drop`), and the commit's own, dropped as it publishes (`ST_wit_commit_var_drop`);
a node is retired while a thread that loaded it is pinned (`ST_wit_guarded_retire`); kovan frees a
node while threads still run (`ST_wit_early_free`); and, under fair scheduling, two transactions
that each read what the other writes abort each other forever (`ST_wit_livelock`: each locks its
write, takes the clock, finds the other's lock on the variable it validates, releases and
retries).

## Configurations

| configuration | threads | transactions |
|---|---|---|
| `ST_transfer3` | three | a transfer between x and y; a read of both, then an increment of y; an increment of x |
| `ST_cross3` | three | x read and y written; y read and x written; a read of both |
| `ST_incr3` | three | an increment of x each |
| `ST_rounds` | two | x read, x and y written, then a read of both; an increment of y, then of x |
| `ST_drops` | two | a store replaced by a second, both rolled back by a retry; y read, its handle dropped, x written; z written, its handle dropped; against a read of x, then an increment of x |
| `ST_reread_quiet` | two | x and y read, x read again, y written; against an increment of y, then a read of both |
| `ST_live` | two, fair | as `ST_rounds`; `Termination` |
| `ST_live_cross` | two, fair | the first two threads of `ST_cross3`; `SoloEnds` |
| `ST_reread` | two | x read twice; against a store to x |
| `ST_reread_update` | two | x read twice, y written; against a store to x |
| `ST_reread_torn` | two | x, y, then x read; against a store to both |
| `ST_reread_stable` | two | as `ST_reread_torn`: a repeat load never meets a stable version other than its first's |

The mutations and witnesses run the programs of the passing configurations: `ProgTransfer` (the
first two threads of `ST_transfer3`) for `keep_locks`, `keep_locks_live`, `free_now`,
`no_rv_check`, `version_before_swap` and `read_only_not_committed`; `ST_drops`'s for
`no_keep_alive`; `ST_live_cross`'s for `skip_read_validation` and `stale_read_version`; and
`ProgCommitted` (one thread committing x twice, as `tests/drops.rs` does) for
`commit_copies_value` and `no_var_retire`; the three `reread_unvalidated` ones run the programs of
`ST_reread`, `ST_reread_update` and `ST_reread_torn`. The witnesses run `ST_transfer3`'s, except
`validate_abort` (`ST_cross3`), `reread` (`ST_reread_quiet`), `reread_retry` (`ST_reread`),
`entry_drop` and `commit_var_drop` (`ST_drops`) and `livelock` (`ST_live_cross`).

## Code map

| label | function | code | step |
|---|---|---|---|
| `TX` | `Stm::atomically`, `Transaction::new` | `lib.rs:80-85`, `transaction.rs:127-138` | the pin, the clock loaded (the read version); at the program's end the handles dropped (`TVarInner::drop`, `var.rs:57-65`) |
| `OP` (load) | `Transaction::load`, `load_version_lock` | `transaction.rs:190-197`, `var.rs:46-49` | the lock word: locked or newer than the read version, `Retry`; a repeat load too |
| `OP` (private) | `Transaction::load`, `Transaction::store` | `transaction.rs:179-188`, `transaction.rs:240-255` | a load of a variable written, a store |
| `OP` (retry) | `Stm::atomically`, `Transaction::drop` | `lib.rs:110-123`, `transaction.rs:113-124` | the closure's `Err(Retry)`: the transaction dropped, the guard dropped |
| `OP` (handle) | `TVarInner::drop` | `var.rs:57-65` | the closure drops its handle; the last reference drops the variable |
| `OP` (commit) | `Transaction::commit` | `transaction.rs:259-273`, `transaction.rs:276-278` | read-only: committed, the hooks, the drops; otherwise the first write's lock word loaded |
| `RD2` | `Transaction::load` | `transaction.rs:200` | the pointer loaded |
| `RD3` | `Transaction::load` | `transaction.rs:202-224` | the lock word again: changed or locked, `Retry`; the read entry recorded, or a repeat load's version checked against it |
| `RD4` | `Transaction::load` | `transaction.rs:226-230` | the node's value cloned |
| `LK1` | `Transaction::commit` | `transaction.rs:276-286` | the next write's lock word loaded; held by another: abort, releasing `range(..id)` |
| `LK2` | `Transaction::commit` | `transaction.rs:287-307` | the lock's compare-and-swap; a failure on a locked word aborts; a variable read and written since aborts, releasing `range(..=id)` |
| `CK` | `Transaction::commit` | `transaction.rs:310-324` | the clock's fetch-add: the write version |
| `VA` | `Transaction::commit` | `transaction.rs:326-354` | a read entry's lock word: locked or newer, abort, releasing every lock |
| `PB1` | `Write::commit` | `transaction.rs:67-80` | the fresh node swapped in, the replaced one retired |
| `PB2` | `Write::commit` | `transaction.rs:81-83` | the version stored (the lock released); the entry's reference dropped (`TVarInner::drop`, `var.rs:57-65`, for the last one) |
| `FIN` | `Transaction::commit`, `Stm::atomically` | `transaction.rs:361-369`, `lib.rs:91-93` | committed, the commit hooks, the transaction dropped, the guard dropped |
| `UL` | `unlock` | `transaction.rs:89-93` | a lock released (`fetch_and(!1)`); after the last, the transaction and the guard dropped |
| `RC1` | kovan | `retire_node` (`kovan/src/node.rs:149-160`), the guard's drop | a retired node freed, its value dropped, once every guard pinned at its retirement dropped |

## TLC results

The run recorded in `tlc-run.txt` (4 workers for a passing configuration, one for a violation,
at the lowest priority on a 36-core machine shared with other heavy work): 38 of 38
configurations match `EXPECTED.txt`, in 143 s of TLC time. The passing ones are `ST_transfer3`
(809,342 distinct states, 33 s), `ST_cross3` (299,799, 12 s), `ST_drops` (271,237, 12 s),
`ST_incr3` (130,657, 6 s), `ST_rounds` (81,426, 4 s), `ST_live` (81,426, 22 s, with
`Termination`), `ST_reread_quiet` (7,392, 1 s), `ST_live_cross` (2,848, 3 s, with `SoloEnds`) and
the four `ST_reread*` ones (at most 1,490 each). Every run that breaks a property stops within
8,437 distinct states and 4 s. `ST_wit_livelock` breaks `Termination` on the 2,848 states on which
`ST_live_cross` passes `SoloEnds`: the schedule that keeps both transactions aborting lets either
one finish once the other is done.
