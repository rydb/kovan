# TLA+ models of kovan

Six models, each at the grain of its code's atomic steps, checked by TLC: kovan's memory
reclamation (the `kovan` crate) and its magazine cache and slab layer (the `recycle` feature), the
two concurrent maps of `kovan-map` and the segment queue of `kovan-queue`. Each carries the defects fixed so far as mutations, one at a time (the maps' 0.1.20
rules and the fixes merged into this branch, the reclamation's 0.1.21 rules and the later defects
this branch fixed, the segment queue's earlier pop): TLC finds a counterexample for every one, and
none for the code as built.

| where | what | run |
|-------|------|-----|
| `reclaim/` | `kovan`'s memory reclamation: the global epoch, each thread's reservation and helper slots, pin (the drained-epoch skip, the transition attempts, the helped slow path and the detach of its slot list), the protected load (the raise, the escalation to the unconditional reservation), the guard's drop, retire (batches, their placement in the eligible slots, the count, the merge of a batch that cannot be placed), the traversal and the free-list cache, destructors that pin, load and retire from inside a free, flush, a thread's exit (two rounds, the deactivation, the batches parked on its tid) and the tid's hand-over, and the recycling of retired nodes through a pool (`retire_reclaimable`: the destructor that hands a node to the pool, the take, the re-initialised header, each node's incarnations) | `just tla reclaim` (32 to 73 minutes in the recorded runs, by the machine's load) |
| `chained/` | `kovan_map::HashMap`, the chained map: link words with a deleted mark, a frozen flag and a held flag, one CAS per write, the unlink-then-retire rule, the walk that steps past a deleted node only through a live link, the conditional writes that hold the key's link while their closure runs, the freezing migration (which waits for a hold) and clear, the bucket-snapshot walk | `just tla chained` (about 23 minutes) |
| `hopscotch/` | `kovan_map::HopscotchMap`: home buckets with hop bits, writer guard and move stamp, the guarded insert (existence scan, the bit published before the link, displacement toward the home), the guarded remove, the conditional writes (closure under the home guard, a compute of an absent key reserving its slot first), the lookup that rescans on a moved stamp, the resize that holds every writer guard, the clear, the walk across a table swap, the shrink a remove asks for and its threshold (the table's shrink word) | `just tla hopscotch` (about 3 minutes in the recorded run) |
| `segqueue/` | `kovan_queue::SegQueue`: the two claim words and segment pointers, the push's fetch-add claim and the cell's compare-and-swap, the link of a successor holding the linking push's value, the tail word's and pointer's advance, the pop's view of the two words, its fetch-add claim and swap (a cell still being written taken out of play), the `try_pop` claim by compare-and-swap and its `Busy` answer, the drained head segment's successor found, the head's walk that moves the tail pointer off a segment before retiring it, and kovan freeing a retired segment after its holders | `just tla segqueue` (about 25 minutes in the recorded run, on 4 workers) |
| `magazine/` | the `recycle` feature's magazine cache for one class: each thread's loaded and previous magazines and their swaps, the depot's two Vyukov rings at their atomic steps (ticket, turn word, the ticket's compare-and-swap, the magazine, the published turn), the refill from the layer below, the hand-off of a full or empty magazine and the release of one the depot has no room for, a thread's exit | `just tla magazine` |
| `slab/` | the slab layer under the magazine cache: an owner's chunks, its free lists and its spare chunk, the inbox other threads push blocks on, the owner's drain, its exit (the counts, the close and its count-downs), the last block back freeing an orphaned chunk and the inbox | `just tla slab` |

`just tla-all` runs every family (each directory of `proofs/tla/` with an `EXPECTED.txt`), and
`just tla <family> [configuration...]` one family, or only the configurations named; both run
`proofs/tla/run_tlc.sh` (`bash proofs/tla/run_tlc.sh all`, `... <family>`). The script takes the
TLA+ tools from `$TLA2TOOLS` when set, otherwise from `proofs/tla/.tools/tla2tools.jar`, which
it fetches on first use (release v1.7.4, TLC 2.19, the version of every recorded run).
`TLC_WORKERS` caps the workers of a passing configuration (default: TLC's `auto`), `TLC_LIMIT` the
seconds each configuration may take (default 3600). A configuration expected to break a property
runs one worker, so the breadth-first trace is the shortest, and the trace is kept in
`<family>/<configuration>_counterexample.txt`. Each family's `EXPECTED.txt` names what every
configuration must report, and a full run of a family rewrites its `tlc-run.txt`. CI runs the
same: `.github/workflows/tla.yml` runs `.github/workflows/tla.sh` on every push to and pull request
against `master`, which fetches tla2tools.jar v1.7.4, checks its SHA-256 and hands it to
`proofs/tla/run_tlc.sh all` through `TLA2TOOLS`.

## The core reclamation (`reclaim/Reclaim.tla`)

### What is modelled

kovan's memory reclamation (`kovan/src/guard.rs`, `reclaim.rs`, `slot.rs`, `retired.rs`,
`atomic.rs`) as the code runs it. The state: the global epoch and the slow-path counter; each
thread's slots, the reservation (index 0) and the helper slot (`hr_num + 1`), each a list word
(`first`) and an era word (`epoch`) whose high halves are sequence numbers; each thread's help
request (`state[0].result`); the nodes with their `next`, `batch_link`, `refs_or_next` and birth
epoch; each thread's handle (the pin count, the accumulating batch and its count, the allocation
counter, the free-list cache and its count, the cached, drained and birth epochs, `in_reclaim`,
the tid); the word of released tids, each tid's orphan word and the count of tids holding orphans;
with `Recycle`, the pool of freed nodes and each node's incarnation (a ghost).

The model is written in PlusCal: `pcal.trans` writes the TLA+ translation below the algorithm
(edit the algorithm, run `java -cp proofs/tla/.tools/tla2tools.jar pcal.trans -nocfg
proofs/tla/reclaim/Reclaim.tla`, and delete the `Reclaim.old` it leaves). Each label is one step:
one atomic instruction of the code, with the thread-local work before or after it (handle cells,
the nodes of the thread's own unsubmitted batch or of a chain it took, a batch whose count is zero,
which no other thread reaches). Fences are not steps: the model is sequentially consistent, and
the SeqCst fences that pair a slot's publication with a submission's scan are what make the
hardware behave as that interleaving on these paths. A `WordPair::load` is two steps, the low word
then the high one, as on the native targets; a compare-exchange of the pair is one step.

Every operation runs through the steps of its code: `pin` (the outermost pin's compare with
`drained_epoch`; `transition`'s attempts of `do_update`, then `slow_path`: the request, the passes
that self-complete or traverse the list and republish the era, `detach_nodes` unless the loop found
the list detached, the republication of the answer, the drain); `help_read` and `help_thread` (the
request read, the passes of `do_update` on the helper slot, the answer, `detach_nodes`, the
hand-over of the era and of the list's sequence number, the helper slot left); the protected load
(`protect_load`, `protect_load_cold`: the raises, the escalation) and `load_unprotected`; the
guard's drop (`unpin`, `unpin_outermost`); retire (`enqueue_node`, `take_batch`, `try_retire`'s
scan and inserts, the rollback of an insert into a deactivated slot, the traversal of a list an
insert displaced, `merge_batch`, `increment_era`); `traverse`, `traverse_into_cache`,
`traverse_onto_cache`, `free_batch_list`, `drain_free_list`; `flush` (on a thread with no tid, the
tid it claims while a tid holds orphans or its own batch holds a value; the own list,
`adopt_orphans`, the submission that leaves the own slot out, `increment_era`, the drain, the
release of the reservation); a thread's exit (`cleanup`: on a thread with no tid whose batch holds
a value, the tid it claims first; the rounds of submitting, taking the own list and freeing, the
last batch parked, `deactivate_slots`, the captured lists traversed, `park_orphans`,
`release_tid`); `alloc_tid`.

Procedures carry a call stack per thread, so the operations a destructor runs happen inside the
free that called it: a drop may pin, load, retire, write and flush (its flush does nothing, as
`in_reclaim` is set), and its pin is nested or outermost by the pin count at that point. A program
is a sequence of operations per thread (`MC_Reclaim.tla`): pin, the guard's drop, a protected and
an unprotected load of a shared cell, a write (a node allocated, the cell swapped to it, the old
value retired), a retire of a node never published, flush, and the thread's exit. Scheduling
operations (`After`, `Join`, `AwaitRel`) only order a scenario's threads, as a test that spawns
threads at chosen points does. A pointer loaded under a guard is held until that guard drops; the
pointers a drop loads die with the drop's own guard.

Recycling of retired nodes (`retire_reclaimable` with a `Reclaimable::dealloc` that puts the
node on a free list, the constant `Recycle`): see "Recycling nodes" below.

Not modelled, and why:

- The object hand-over of the slow path and of `help_thread` (the `pointer` and `parent` words,
  the parent slot `hr_num`, a refs-node put into a slot list as its terminal entry): kovan's pin
  always requests with `pointer = 0` and `parent = 0`, and no other code writes those words, so
  those branches never run and the parent slot stays inactive. The model reads the answer's
  pointer half and checks that it is 0 (`WellFormed`).
- Memory orderings (see above), and the fallback `WordPair` of targets without native 128-bit
  atomics, whose sub-word operations are compare-exchange loops (`lib.rs`: not lock-free there).
- Allocation (`Box::new`, `ensure_page`): a fresh node is allocated in one step, and the
  tids stay below `MaxTid` (65,536 in the code).
- The pool's own code: the free list is the recycler's (the example in `reclaim.rs` is a
  `Mutex<Vec>`), and the model takes from it and adds to it in one step each, leaving the
  node's words as kovan left them, except where a configuration puts an intrusive pool's link
  in the header (`stale_reuse_link_next`, `stale_reuse_link_birth`). A recycler that writes
  `RetiredNode::new()` at the take overwrites whatever a pool wrote there. A value's drop in
  place is the destructor's program, as for any node. Every node of a configuration with
  `Recycle` recycles, the nodes the cells hold at first included.
- Thread-local storage teardown: a drop that the exit runs reaches the handle, as the code does by
  keeping the exiting handle in `EXITING`; the mutation `exit_handle_unreachable` puts back the
  handle a drop could not reach. No operation runs after a thread's exit, so the model has no
  counterpart of `exit_pending`, which keeps a flush made by a thread-local destructor after the
  exit from claiming a tid that no exit would release. Nor of the nightly build's cleanup
  sentinel: the model's exit always runs, as the stable build's does, while on nightly it runs
  only from a sentinel, which `enqueue_node` registers for a thread with no tid that starts a
  batch (see "Values retired by a thread that never pinned").
- The epoch never wraps; the state constraint bounds it (`MaxEpoch`). The code's constants are
  scaled per configuration: `RETIRE_FREQ`, `EPOCH_FREQ`, `MAX_CACHE`, `MAX_LOAD_ATTEMPTS`, the 16
  transition attempts and `EXIT_ROUNDS`.

### Properties

- `NoUseAfterFree`: a pointer a thread loaded under a guard is not freed before that guard drops
  (a destructor's own guard for what a destructor loads), and the reclamation never reads or writes
  a freed node. With `Recycle` a pointer names the incarnation it loaded, and the node keeps that
  incarnation until the guard drops (neither handed to the pool nor taken out again), and the
  reclamation reads or writes no node outside the retirement it frees: none in the pool, none
  live again. `ListsHoldNoFreed`: no slot list holds a freed node (with `Recycle`, one in the
  pool or live again).
- `NoDoubleFree`: no destructor runs twice. `NoNullDeref`: a retire at a batch boundary finalizes
  the batch its cells hold, never an emptied one.
- `NoLoss`: when every thread has exited, every retired node is freed or in a batch parked on a
  tid, for a later flush to adopt. `NoLoss` counts a parked batch as kept; that a flush does adopt
  it is `OrphansAdopted` (`RC_live_orphan`, a liveness property): every batch an exit parked is
  eventually adopted, by a flush on a thread that never pinned too (see "A flush on a thread that
  never pinned" below). A value left in the batch of a thread that has exited is in no orphan
  chain, so `NoLoss` does see it lost (`RC_mut_exit_skips_batch`). `RetiredFreed`
  (`RC_live_unpinned_flush`, a liveness property): every retired value is eventually freed, also
  one that a thread retired without pinning and then flushed while it lives on (see "Values retired
  by a thread that never pinned" below).
- `PinDrains`: an outermost pin traverses its slot list whenever the global epoch is not the one the
  slot published at its last drain. `DrainLive` (`RC_live_drain`, a liveness property): a thread
  that keeps pinning eventually releases every node its retires put in its own slot.
- `EscalationBounded`: no thread holds the unconditional reservation outside the critical section
  that escalated. `CacheBelowPublished`: in a section, a thread's cached epoch never exceeds the
  epoch its slot publishes, so the protected load's one compare is sound.
- `BirthFresh`: a thread that advanced the epoch stamps its later allocations with that epoch or a
  later one, so a batch it retires afterwards skips the slots that publish older epochs.
  `FlushReleases`: after a flush with no guard live, the thread's reservation publishes epoch 0
  until it pins again, so no batch retired from then on waits for it.
- `DetachNotStarved`: a detach of a slot list fails only for the try_retires already past their
  scan when it closed the era: no scan that reads the era while a detach of the list at its tag is
  in progress inserts into the list.
- `WellFormed`: kovan never puts an RNODE-marked or INVPTR word at the head of a list, and never
  hands over a pointer.
- `LoopBounds` and `WaitFree`: see below. `Termination` (`RC_live`, weak fairness for every
  thread): every program ends. `Thread2Ends` (`RC_live_stall`): see below.
- Witnesses (`RC_wit_*`): each asserts that a case never happens, and TLC's counterexample shows
  that the configurations reach it.

### Wait-freedom

`LoopBounds` holds every loop to the bound its code states, T being the thread IDs handed out
(`MaxTid`): a slow path passes its loop at most T + 2 times and a `help_thread` as many; the
hand-over epoch loop makes at most two compare-exchanges; a detach retries only for the
try_retires past their scan when the era closed, one per thread and nesting level of its
destructors (`DetachBound` = 2 + threads x (1 + drops with a program)); `alloc_tid` claims at most
one bit per released id and retries its compare-exchange at most once per id another thread
took; an exit runs `EXIT_ROUNDS` rounds. The pass counters count where `CountSteps` is set (the
`RC_wf_*`, `RC_hand_over` and `RC_help_follows` configurations and the configurations that break
a bound); elsewhere `LoopBounds` checks only the exit's rounds. `help_thread`'s bound rests on the
era's seqno check this branch added (see Findings).

`WaitFree` bounds every operation's steps. `wf[t]` keeps one count per operation in progress on
thread t, its own program's and each destructor's; a step counts for the innermost operation, so
a destructor's operations are counted on their own, each against its own bound. The bound
(`OpBound`) depends on T, the constants and the retirement history only: a protected load takes at
most 3 x `LoadAttempts` + 1 steps (a raise, a load and an epoch read per attempt, then the load
after escalating) and an unprotected load one; pin, the guard's drop, a write or retire, flush and
exit take their `*Ctl` term plus 16 x `Hist` (flush's and exit's terms count a tid claim, which a
flush or an exit on a thread with no tid makes while it has something to submit or adopt;
`RC_flush_orphan`, `RC_wf_unpinned_flush` and `RC_wf_unpinned_exit` count the steps of such
claims). `Hist` = node objects x (1 + threads) bounds the
placements of nodes into slot lists (a node is placed at most once per submission of its batch:
the first, and one more per exit that re-arms it), and each placement costs at most 16 steps over
its life (its insert, the traversal that takes it, its free). Without `Recycle` the node objects
are the node ids (`MaxNodes`). With `Recycle` every take from the pool starts one more object,
so the objects are `MaxNodes` plus the sum of every id's incarnation count, evaluated in the state
checked; a write or a retire of a fresh node also takes one step more, the take (`TakeCtl`). The `*Ctl` terms count every other step,
label by label (`Reclaim.tla`): for instance a slow path takes 5 steps to publish its request,
at most T + 2 passes of 8 steps and a traversal's last step each, then either the self-completion
(4 steps and a drain) or the detach and the republication (9 steps, a detach of at most
1 + 3 x `DetachBound` steps, a traversal and a drain); a `help_thread` takes 4 steps to read the
request, at most T + 2 passes of a `do_update` and 5 steps, then the answer, a detach, the
hand-over and the helper slot left (10 steps, a detach, two traversals and a drain).

Counting objects rather than ids is what makes the bound hold under recycling: the argument for
16 steps per placement is about one life of a node, and one operation can, in principle, free
more objects than there are ids, since the drops it runs can take back a node it freed and
retire it again (an argument; the configurations here are too small to tell the two counts
apart, TLC finding the id count respected too). `RC_wf_recycle` and `RC_wf_recycle_dtor` check
`LoopBounds` and `WaitFree` with recycling on: a reader with a writer whose later writes take
back freed nodes, and a drop that takes back, inside the walk that freed it, the node freed a
step before; `RC_wit_wf_reuse` and `RC_wit_wf_dtor_reuse` show both reuses happen in those
exact settings. The loop bounds do not change with recycling: only the detach bound involves
nodes, through the nesting of destructors counted per id, and an id's next life starts only
after its destructor ended, so an id never nests inside its own destructor.

A stalled thread delays no one: `RC_live_stall` schedules only thread 2 fairly and lets thread 1
stop for good at any step of its exit, the park of its orphans and the release of its tid
included, and thread 2's first pin, load, retire and flush still end (`Thread2Ends`). `RC_wf_pin` and
`RC_wf_load` count steps against a thread that moves the epoch at every flush or retire. The
mutations take each mechanism a bound rests on out: `no_help` (a slow path passes T + 3 times),
`no_escalate` (a load retries without bound), `help_follows_next_request`,
`help_no_seqno_check`, `detach_unclosed`, `exit_loop` and `ttas_locks` (a thread stopped holding a
lock stops every first pin).

### Recycling nodes (`retire_reclaimable`)

#### A worked story

One `Atomic` cell holds node A. Every node starts with a header, a `RetiredNode`, which records
the epoch at which the node was created (its birth epoch).

1. A reader pins (`kovan::pin()`). Its reservation slot now publishes the current global epoch,
   say 3. It loads A from the cell and keeps the pointer while its guard lives. The model writes
   down what the reader holds: A, incarnation 0.
2. A writer swaps a new node B into the cell and calls `retire_reclaimable(A)`. A goes into the
   writer's batch. When kovan submits that batch, it gives one node of the batch to each active
   slot whose published epoch is at least the batch's earliest birth epoch (`try_retire` in the
   code map has the exact checks). A was created no later than epoch 3 (it was already in the
   cell when the reader loaded it under epoch 3), so the reader's slot gets one. The batch
   counts how many slots hold one of its nodes. (A batch with fewer nodes than such slots is
   kept back and submitted later with more nodes; until then A is not freed either.)
3. The writer goes on: it flushes, and the epoch moves to 4, then 5. A stays where it is: its
   batch's count is not zero while the reader's slot holds a node of it.
4. The reader drops its guard, and later pins again. Since the epoch moved, that pin walks its
   slot list and lowers the batch's count; when the count reaches zero the batch is freed. To
   free node A, kovan first reads what it still needs from A (the next node of the batch, the
   destructor), then calls `<Node as Reclaimable>::dealloc(A)`, which drops A's value and puts A
   on the pool, the structure's free list. From then on kovan never touches A again.
5. The writer's next write takes A from the pool, writes `RetiredNode::new()` over its header
   (fresh words, and a birth epoch from the writer's own cached epoch) and stores it in the cell.
   Same address, new object: the model calls it A, incarnation 1. A reader that loads it now
   holds A, incarnation 1.

Why the reader of step 1 was safe: A could reach the pool only once the reader's slot let go of
A's batch, and the slot lets go only when the reader pins again, after its guard dropped. So for
as long as the reader held A, incarnation 0, A was neither in the pool nor reused. The model
checks exactly this rule (`NoUseAfterFree`): every pointer a thread holds names a node that is not
in the pool and still has the incarnation the load returned. TLC checks it in every interleaving
of the configurations below, which have two threads, a few nodes and epochs up to 10: evidence
for those scenarios, not a proof for every number of threads and nodes.

If the writer in step 5 skipped `RetiredNode::new()`, A would go out with the header of its first
life, birth epoch included. The first version of the recycling docs in `reclaim.rs` said memory
safety does not depend on that write; the model checks that claim, "What TLC found" below says
where it holds and where it does not, and the docs now require the write.

#### What the model adds

- The constant `Recycle`. When it is TRUE, every node is retired with `retire_reclaimable` and
  its `dealloc` recycles it. When it is FALSE, none of the steps below ever runs: the 85
  configurations that do not recycle set it FALSE and keep their meaning (see "TLC results" for
  the state counts).
- The pool (`pool`): the nodes `dealloc` handed back that no one has taken yet. It is a set, so
  the next take may pick any of them, which covers every order a real free list could hand nodes
  out in. The model takes from it and adds to it in one step each.
- Each node's incarnation (`ninc`): how many times the node was taken from the pool to be used
  again. It is not in the Rust code; the model keeps it to tell "the same address" from "the same
  object". Without it, a node reused under a reader would look like the node the reader loaded.
- The end of every destructor (`Dealloc`), wherever the model already runs destructors (on any
  thread, inside any kovan call that frees a batch: a pin, a guard's drop, a retire, a flush, an
  exit): the node is freed, or with `Recycle` put on the pool.
- The take (`WR1`, `RN1`): a write, or a retire of a node never published, takes a node from the
  pool when the pool holds any, else it allocates a fresh one. The take starts the node's next
  incarnation; the node is the taker's own until it publishes it.
- The fresh header (`WR2`, `RN2`): `RetiredNode::new()` written over the taken node's header (its
  words cleared, its birth epoch stamped from the thread's cached epoch, `guard.rs`
  `current_birth_epoch`, as for a fresh node), then the swap into the cell and the retire of the
  value it replaced, or the retire of the node itself.
- Loads (`LD1`, `LD4`, `LD6`, `LU1`) record the incarnation of the node they return, at the load
  itself, so a reuse between the load and the check after it counts as a different object.

#### What is checked

- `NoUseAfterFree`, made stricter: for every pointer a thread holds, its node is not in the pool
  and still has the incarnation the load returned; and kovan's own reclamation code (the walk
  over a slot list, the free of a batch, a retire's inserts) never reads or writes a node that is
  in the pool or in use again. Before recycling the rule was only "not freed", which a reused
  node would pass.
- `ListsHoldNoFreed`, made stricter the same way: no slot list reaches a node in the pool or in
  use again.
- `WaitFree`, with its bound counting node objects: every operation, and every operation a drop
  runs, ends within its step bound, which counts each take from the pool as one more object
  (see "Wait-freedom" above). `LoopBounds` as before.
- Every other property is unchanged and checked as before (`NoDoubleFree` also catches a second
  `dealloc` of a node already in the pool).
- `BirthFresh` checks the birth epochs `RetiredNode::new()` stamps; the configurations that skip
  that write leave it out, since they stamp nothing.

#### The configurations, one by one

All use two threads unless said otherwise, and every node recycles.

- `RC_recycle` (pass). Thread 1 reads cell 1 and holds what it read; thread 2 replaces cell 1
  again and again and flushes in between, so its retired nodes are freed into the pool and taken
  back by its later writes, each with `RetiredNode::new()` written over its header. It checks
  every safety property. It would catch kovan calling `dealloc` while a reader could still reach
  the node (the reader would then see another object at the same address), or kovan touching a
  node after its `dealloc`.
- `RC_recycle_dtor` (pass). Node 1 and a fresh node can be freed in one batch, the fresh one
  first, and node 1's own drop, run inside that walk, reads cell 2 and replaces it, possibly with
  the node the same walk freed a step before; thread 2 replaces and reads cell 2 meanwhile. It
  would catch the walk reading or writing a node after handing it to the pool (the next drop may
  already have reused it), or a reuse inside a drop corrupting the batch being freed.
- `RC_recycle_stale` (pass). `RC_recycle` with the recycler skipping `RetiredNode::new()`
  (stale_reuse): a node goes out again with the header and birth epoch kovan left on it. It checks
  the claim of `reclaim.rs` that memory safety does not depend on the write, and would catch
  kovan reading a stale header word before rewriting it, or a kept birth epoch that lets a batch
  skip the slot of a reader holding the node.
- `RC_recycle_dtor_stale` (pass). The same claim on `RC_recycle_dtor`: the node a drop takes back
  from the walk that freed it keeps the header it had in that batch, its words still describing
  the batch being freed.
- `RC_recycle_stale_link_next` (pass). The same claim with an intrusive pool: no
  `RetiredNode::new()`, and `dealloc` writes the pool's own link into the node's first header word
  (`next`), which the reuse keeps. It would catch kovan reading `next` before rewriting it.
- `RC_recycle_stale_lag` (pass). The same claim on a recycler whose cached epoch lags: thread 1,
  pinned at the first epoch, can take back a node thread 2 stamped with a later epoch and
  publish it with that later epoch, later than its own `RetiredNode::new()` would stamp. It would
  catch a kept birth epoch later than the epoch at which the node is published, which would let
  its batch skip a reader's slot.
- `RC_mut_reuse_retired` (`NoUseAfterFree` must break). A defect in a recycler: it may take a node
  that is still retired (its batch not freed, its `dealloc` not called), as a structure would if
  it reused a node as soon as it unlinked it. The model must see that a reader's pointer now
  names another object; a model blind to reuse would pass here.
- `RC_mut_read_after_dealloc` (`NoUseAfterFree` must break). A defect in kovan: `free_batch_list`
  reads a node's `batch_next` after calling its destructor instead of before. With recycling the
  destructor has already handed the node to the pool and another thread may have taken it. It
  shows the model catches kovan touching a node after `dealloc`.
- `RC_mut_stale_link_birth` (`NoUseAfterFree` must break). No `RetiredNode::new()`, and `dealloc`
  writes the pool's link (a pointer, above every epoch) over the `birth_epoch` word, which
  `reclaim.rs` allows (`dealloc` owns the whole allocation, the header included). It shows where
  the claim that the write is not needed stops holding.
- `RC_mut_pool_lock_held` (must deadlock). A defect in a recycler: its pool has a lock, and a
  write keeps it from taking a node until its retire of the old value returns. One thread. That
  retire frees the old value's batch at once and calls its `dealloc` on the same thread, which
  waits for the same lock: the thread waits for itself.
- `RC_mut_cache_ahead` (`CacheBelowPublished` must break), `RC_mut_early_free`
  (`ListsHoldNoFreed` must break), `RC_mut_help_hands_pointer` (`WellFormed` must break) and
  `RC_mut_drain_published_term` (`Termination` must break). These four give the properties no
  mutation above broke on its own a mutation of their own, so every property the family checks
  has one that breaks it: a raise that caches the epoch it read without storing it in the slot; a
  traversal that frees a batch one decrement early, while a slot list still holds a node of it; a
  helper that hands a pointer over in the result word; and the drain that waits on a published
  reservation, with every thread scheduled fairly. Each checks the other safety properties beside
  its own, listed after it, so the property breaks on its own: TLC stops at the first state that
  breaks any of them, and it names the one that mutation is for. (Checked against these
  properties alone, earlier mutations do break some of them, but only after a use after free
  that breaks `NoUseAfterFree` first.)
- `RC_wit_reuse`, `RC_wit_dtor_reuse`, `RC_wit_stale_reuse`, `RC_wit_stale_later` (each must
  break its witness). They show the passing configurations reach the cases they are for: a
  reader holding a node in its second or a later incarnation; a drop inside a walk taking a node
  from the pool; a node going out with a birth epoch older than `RetiredNode::new()` would stamp;
  and one going out with a birth epoch later than it would stamp. If TLC found none of these, the
  passing configurations would check nothing about them.
- `RC_wf_recycle` (pass). Step counts with recycling: a cut-down `RC_recycle` (thread 1 reads
  cell 1 in two guards, thread 2 replaces it three times and flushes between), every operation's
  steps counted. It checks `LoopBounds` and `WaitFree` with the bound counting node objects, and
  would catch a recycling path that makes an operation loop or wait beyond those bounds.
- `RC_wf_recycle_dtor` (pass). Step counts with reuse inside a walk: a cut-down
  `RC_recycle_dtor`, node 1's drop taking back, inside the walk that frees its batch, the node the
  same walk freed a step before. It checks `LoopBounds` and `WaitFree`, the walk's operation and
  each operation the drop runs counted on their own.
- `RC_wit_wf_reuse`, `RC_wit_wf_dtor_reuse` (each must break its witness). In the two
  step-counted settings exactly: a reader holds a node in a later incarnation, and a drop inside
  a walk takes a node from the pool, so the two checks above really count steps through reuse.

#### What TLC found

With `Recycle` the code as built passes (`RC_recycle`, `RC_recycle_dtor`): in these scenarios a
pointer a guard holds keeps its incarnation until the guard drops, and kovan reads or writes no
node once its destructor ran, also when a drop the walk runs takes back from the pool the node
the same walk freed a step before (`RC_wit_dtor_reuse` shows that case is reached). With step
counts on (`RC_wf_recycle`, 1,638,997 distinct states; `RC_wf_recycle_dtor`, 1,639,234), every
operation stays within its step bound and every loop within its bound, the bound counting node
objects. About the contract in the Recycling nodes section of `reclaim.rs`:

- **Skipping `RetiredNode::new()` is safe only while the header is the one kovan left.**
  `RC_recycle_stale`, `RC_recycle_dtor_stale`, `RC_recycle_stale_lag` and
  `RC_recycle_stale_link_next` pass; `RC_mut_stale_link_birth` breaks `NoUseAfterFree` (121,028
  states). The first version of these docs said memory safety does not depend on the write. That
  holds while the header is the one kovan left: retirement rewrites `batch_link` and `refs_or_next` (and the
  destructor, which the model does not keep in the node) before anything reads them, `next` is
  written before each read (reset before the node enters a slot list, set on a refs-node before
  it serves as a free-list or orphan link), and a kept `birth_epoch` is one kovan stamped or
  lowered, never later than the global epoch when the node goes out again, so never later than
  the epoch a reader publishes before it loads the node. It holds as well for a pool that links
  its nodes through `next`. But the same docs give `dealloc` the whole allocation, "the
  embedded `RetiredNode` included", and a pool whose link lands on the `birth_epoch` word sends
  the node out with a pointer for its birth epoch. The batch it is retired in then has an
  earliest birth above the epoch of every reservation that has not escalated, and the retire
  frees it at once. In the counterexample thread 1 loads node 1 in its second incarnation under a
  reservation at epoch 3; thread 2 replaces and retires it, its scan skips thread 1's slot, and
  the batch is freed while thread 1 still holds node 1. The claim needed a condition those docs
  did not state: nothing but kovan wrote the header since the node's last retirement. The docs
  now require the write instead.
- **A kept birth epoch can be later than the stamp it stands in for** (`RC_wit_stale_later`;
  `RC_recycle_stale_lag` passes). The first version of the docs presented a kept epoch as older
  than a fresh stamp (it "can only make kovan defer a batch"). A thread whose cached epoch lags (thread 1, pinned at the
  first epoch) can take back a node another thread stamped later; skipping the write then keeps
  the later epoch, so the node's batch is given to fewer slots than the write would give it. In
  `RC_recycle_stale_lag` that never let a batch go too early: the kept epoch is still at most the
  global epoch when the node goes out.
- **A walk that reads a node after its destructor** (`RC_mut_read_after_dealloc`, 216,939 states):
  thread 1's drain frees node 2 into the pool, thread 2's write takes it (its second
  incarnation), and only then does thread 1's walk read node 2's `batch_next`, a word thread 2 is
  about to overwrite with the new header. `free_batch_list` reads everything it needs from a node
  before `d(curr)`, as the comment this branch added there says, and with that order the
  passing configurations find no such read.
- **A recycler that takes a node still in a batch** (`RC_mut_reuse_retired`, 6,827 states):
  thread 2's second write takes node 1 out of thread 2's own unsubmitted batch, before any
  destructor ran, while thread 1 holds node 1: the pointer thread 1 holds now names another
  incarnation.
- **A pool lock held across a call into kovan** (`RC_mut_pool_lock_held`, a deadlock after 58
  states): a write with no guard takes node 1 back holding the pool's lock and retires the value
  it replaced; no slot holds that batch, so the retire frees it at once, and its `dealloc` waits,
  on the same thread, for the lock the write holds. `reclaim.rs` states the rule (never hold the
  free list's lock across a call into kovan); the trace shows the retire itself is such a call.

### Code map

Every label of the algorithm, with the function and the lines of `kovan/src` it models, as of the
commit that last changed this table. The model-only labels are the scheduling of a scenario's
threads and the steps that exist only under a mutation (the lock steps of `ttas_locks` take a step
that does nothing without it).

| label | function | code | step |
|---|---|---|---|
| `TidClaim` | `alloc_tid` | `slot.rs:594` | next_tid.load: the ids handed out |
| `TidClaim2` | `alloc_tid` | `slot.rs:596` | a release word loaded |
| `TidClaim3` | `alloc_tid` | `slot.rs:598-604` | fetch_and of the lowest bit seen |
| `TidFresh` | `alloc_tid` | `slot.rs:611-621` | next_tid.load (the page ensured) |
| `TidFresh2` | `alloc_tid` | `slot.rs:626-629` | the strong compare_exchange |
| `TidRelease` | `release_tid` | `slot.rs:671` | one fetch_or |
| `OrphanTake` | `park_orphans` | `slot.rs:702` | the orphan word swapped to null |
| `OrphanPublish` | `park_orphans` | `slot.rs:705-706` | the tail linked, the joined chain stored |
| `OrphanCount` | `park_orphans` | `slot.rs:708` | the `ORPHANED` count's fetch_add |
| `OrphanAdopt` | `adopt_orphans` | `slot.rs:721` | orphans_parked: one load of `ORPHANED` |
| `OrphanAdopt2` | `adopt_orphans` | `slot.rs:724` | max_threads |
| `OrphanAdopt3` | `adopt_orphans` | `slot.rs:726` | a tid's orphan word loaded |
| `OrphanAdopt4` | `adopt_orphans` | `slot.rs:730` | swapped to null |
| `OrphanAdopt5` | `adopt_orphans` | `slot.rs:732` | the `ORPHANED` count's fetch_sub |
| `OrphanMerge` | `Handle::adopt_orphans` | `guard.rs:1230-1238` | each batch of the chain merged (merge_batch) |
| `TV1` | `traverse` | `reclaim.rs:262-281` | the end of the list; next swapped with INVPTR |
| `TV2` | `traverse` | `reclaim.rs:289` | batch_link.load |
| `TV3` | `traverse` | `reclaim.rs:290-295` | refs fetch_sub; the count's last decrement pushes the batch |
| `DS1` | `free_batch_list` | `reclaim.rs:331-338` | the destructor called |
| `DS2` | `drop_boxed`, `dealloc_reclaimable` | `guard.rs:2089-2095` | the value's drop, then its memory freed or (Recycle) the node handed to the pool |
| `FB1` | `free_batch_list` | `reclaim.rs:312-346` | one node: the batch words, batch_next, its destructor called |
| `TC1` | `traverse_into_cache` | `guard.rs:1459-1463` | a full cache taken out of its cell and freed |
| `TC2` | `traverse_into_cache` | `guard.rs:1464-1466` | in_reclaim restored; traverse_onto_cache |
| `DF1` | `drain_free_list` | `guard.rs:1494-1508` | in_reclaim; the cache taken out of its cell and freed |
| `DF2` | `drain_free_list` | `guard.rs:1500-1511` | again until the cell stays empty |
| `DU1` | `do_update` | `guard.rs:460` | first.load_lo |
| `DU2` | `do_update` | `guard.rs:462-464` | exchange_lo(0); the list traversed |
| `DU3` | `do_update` | `guard.rs:467` | epoch() after the traversal |
| `DU4` | `do_update` | `guard.rs:468-483` | store_lo(curr_epoch), fence, mirror_transition |
| `DetachEra` | `detach_nodes` | `guard.rs:767` | the era's compare_exchange_hi(tag, tag + 1) |
| `DetachList` | `detach_nodes` | `guard.rs:771` | first.load(): lo |
| `DetachList2` | `detach_nodes` | `guard.rs:772-773` | then hi; taken by the other detach |
| `DetachList3` | `detach_nodes` | `guard.rs:778-781` | compare_exchange (lo, tag) -> (0, tag + 1) |
| `SP1` | `slow_path` | `guard.rs:605-608` | in_reclaim; prev_epoch = epoch.load_lo |
| `SP2` | `slow_path` | `guard.rs:609` | inc_slow |
| `SP3` | `slow_path` | `guard.rs:612-616` | the state words stored 0; seqno = epoch.load_hi |
| `SP4` | `slow_path` | `guard.rs:619-621` | result.store(INVPTR, seqno): hi (WordPair::store) |
| `SP5` | `slow_path` | `guard.rs:621` | then lo |
| `SL1` | `slow_path` | `guard.rs:642-643` | epoch() compared with prev_epoch |
| `SL2` | `slow_path` | `guard.rs:647` | the self-completion CAS |
| `SL2a` | `slow_path` | `guard.rs:650` | epoch.store_hi(seqno + 2) |
| `SL2b` | `slow_path` | `guard.rs:651` | first.store_hi(seqno + 2) |
| `SL2c` | `slow_path` | `guard.rs:652-662` | dec_slow, mirror_transition, fence, drain_free_list |
| `SL2d` | `slow_path` | `guard.rs:662-664` | in_reclaim restored |
| `SL3` | `slow_path` | `guard.rs:671` | first.load_lo |
| `SL4` | `slow_path` | `guard.rs:673` | exchange_lo(0) |
| `SL5` | `slow_path` | `guard.rs:675-680` | first.load_hi: detached (produced); else onto the cache |
| `SL5b` | `slow_path` | `guard.rs:682` | epoch() read again |
| `SL6` | `slow_path` | `guard.rs:687-688` | the era DCAS (prev, seqno) -> (curr, seqno) |
| `SL7` | `slow_path` | `guard.rs:690-692` | result.load_lo: answered |
| `DN1` | `slow_path` | `guard.rs:699-701` | detach_nodes unless produced |
| `Produced` | `slow_path` | `guard.rs:706` | result.load_hi |
| `Produced2` | `slow_path` | `guard.rs:707` | epoch.store_lo(result_epoch) |
| `Produced3` | `slow_path` | `guard.rs:708-712` | epoch.store_hi(seqno + 2), mirror_transition, fence |
| `Produced4` | `slow_path` | `guard.rs:713` | first.store_hi(seqno + 2) |
| `DN9` | `slow_path` | `guard.rs:718-730` | result.load_lo; the hand-over branch, never taken |
| `DN10` | `slow_path` | `guard.rs:734-738` | dec_slow; the list onto the cache |
| `DN11` | `slow_path` | `guard.rs:741` | drain_free_list |
| `DN12` | `slow_path` | `guard.rs:742` | in_reclaim restored |
| `HR1` | `help_read` | `guard.rs:795` | slow_counter |
| `HR2` | `help_read` | `guard.rs:799` | max_threads |
| `HR3` | `help_read` | `guard.rs:806-808` | each result.load_lo; help_thread |
| `HT1` | `help_thread` | `guard.rs:842-844` | result.load(): lo; nothing to help unless pending |
| `HT2` | `help_thread` | `guard.rs:842` | then hi |
| `HT3` | `help_thread` | `guard.rs:847-861` | state words (0, no parent); seqno = epoch.load_hi |
| `HT4` | `help_thread` | `guard.rs:862` | curr_epoch = epoch() |
| `HelpPass` | `help_thread` | `guard.rs:870` | do_update of the helper slot hr_num + 1 |
| `HT6` | `help_thread` | `guard.rs:874-876` | epoch() compared |
| `HT7` | `help_thread` | `guard.rs:880-883` | the result CAS; detach_nodes |
| `HT10` | `help_thread` | `guard.rs:884-885` | traverse_into_cache |
| `HandOverEpoch` | `help_thread` | `guard.rs:896` | epoch.load(): lo |
| `HandOverEpoch2` | `help_thread` | `guard.rs:896` | then hi |
| `HandOverEpoch3` | `help_thread` | `guard.rs:897-904` | the strong CAS loop |
| `HandOverList` | `help_thread` | `guard.rs:914` | first.compare_exchange_hi(seqno + 1, seqno + 2) |
| `HT12` | `help_thread` | `guard.rs:930` | result.load_lo() |
| `HT12b` | `help_thread` | `guard.rs:933-934` | result.load_hi(); the request the one read first? |
| `HT12c` | `help_thread` | `guard.rs:934` | the era's seqno still the request's: another pass |
| `HelperLeave` | `help_thread` | `guard.rs:940-942` | the helper slot's first.exchange_lo(INVPTR); traversed |
| `HT20` | `help_thread` | `guard.rs:946-968` | the parent words (no parent); drain_free_list |
| `TR1` | `try_retire` | `guard.rs:1271-1280` | max_threads, min_epoch, the fence |
| `TS2` | `try_retire` | `guard.rs:1291` | first.load_lo (reservation slot) |
| `TS3` | `try_retire` | `guard.rs:1297` | first.load_hi odd |
| `TS4` | `try_retire` | `guard.rs:1301` | epoch.load_lo |
| `TS5` | `try_retire` | `guard.rs:1307-1318` | epoch.load_hi odd; a node assigned |
| `TG1` | `try_retire` | `guard.rs:1323` | first.load_lo (helper slot) |
| `TG2` | `try_retire` | `guard.rs:1328-1340` | epoch.load_lo; a node assigned |
| `TN2` | `try_retire` | `guard.rs:1353-1363` | slot info, next null; first.load_lo |
| `TN3` | `try_retire` | `guard.rs:1369` | epoch re-checked |
| `TN4` | `try_retire` | `guard.rs:1378` | exchange_lo(curr) |
| `InsertRollback` | `try_retire` | `guard.rs:1391-1399` | compare_exchange_lo(curr, INVPTR); a node captured counts |
| `TL1` | `try_retire` | `guard.rs:1406` | next CAS null -> prev |
| `TL2` | `try_retire` | `guard.rs:1418-1419` | the list it displaced traversed and freed |
| `TL3` | `try_retire` | `guard.rs:1425` | counted |
| `TF1` | `try_retire` | `guard.rs:1430-1435` | refs fetch_add(adjs); zero frees the batch |
| `TF2` | `try_retire` | `guard.rs:1438` | placed |
| `RE1` | `enqueue_node` | `guard.rs:998-1035` | the node linked into the batch, the count (nightly: a thread with no tid registers its cleanup sentinel, not modelled) |
| `RE2` | `enqueue_node` | `guard.rs:1037-1050` | in_reclaim; take_batch, try_retire |
| `RE3` | `enqueue_node` | `guard.rs:1056-1058` | merge_batch; in_reclaim restored |
| `RE4` | `enqueue_node` | `guard.rs:1068-1071` | alloc_counter; tid() |
| `RE5` | `increment_era` | `guard.rs:1084-1085` | in_reclaim; help_read |
| `RE6` | `increment_era` | `guard.rs:1086-1087` | advance_epoch; the birth stamp |
| `PN1` | `pin` | `guard.rs:527-535` | the count; epoch() vs drained_epoch |
| `PNU` | `transition` | `guard.rs:555` | do_update |
| `PNC` | `transition` | `guard.rs:558-568` | attempts; epoch() compared; slow_path |
| `UP1` | `unpin` | `guard.rs:377-386` | the count; escalated? |
| `UP2` | `unpin_outermost` | `guard.rs:408-410` | count 1, epoch(), do_update |
| `UP3` | `unpin_outermost` | `guard.rs:411` | count 0 |
| `LD1` | `protect_load` | `guard.rs:293` | data.load |
| `LD2` | `protect_load` | `guard.rs:296-311` | epoch() vs cached_epoch |
| `LD3` | `protect_load_cold` | `guard.rs:326-343` | attempts; escalate, or store_lo, fence, cached_epoch |
| `LD4` | `protect_load_cold` | `guard.rs:345` | data.load |
| `LD5` | `protect_load_cold` | `guard.rs:348-352` | epoch() compared |
| `LD6` | `protect_load_cold` | `guard.rs:331` | the load after escalating |
| `LU1` | `Atomic::load_unprotected` | `atomic.rs:140` | data.load, no era check |
| `WR1` | `Atomic::swap` | `atomic.rs:247` | the swap (after RetiredNode::new; then retire); with Recycle and a node in the pool, the take (the recycler's code) |
| `WR2` | `RetiredNode::new`, `Atomic::swap` | `retired.rs:113-120`, `atomic.rs:247` | (Recycle) the taken node's header rewritten, the swap (then retire) |
| `RN1` | `RetiredNode::new` | `retired.rs:118` | a node allocated, its birth stamped (then retire); with Recycle and a node in the pool, the take |
| `RN2` | `RetiredNode::new` | `retired.rs:113-120` | (Recycle) the taken node's header rewritten (then retire) |
| `FL1` | `flush` | `guard.rs:1539-1563` | tid; with none, the own batch and orphans_parked (orphaned.load); in_reclaim, the pin count; with none, tid() claims one |
| `FL2` | `flush` | `guard.rs:1585-1587` | the own list exchanged to 0 |
| `FL3` | `flush` | `guard.rs:1594` | adopt_orphans |
| `FL4` | `flush` | `guard.rs:1595-1597` | take_batch, try_retire |
| `FL6` | `flush` | `guard.rs:1598-1604` | merge_batch; increment_era: help_read |
| `FL7` | `flush` | `guard.rs:1604-1606` | increment_era: advance_epoch, the birth stamp; drain_free_list |
| `FlushClear` | `flush` | `guard.rs:1621-1623` | the own list exchanged to 0 once more |
| `FlushClear2` | `flush` | `guard.rs:1626` | drain_free_list |
| `FlushClear3` | `flush` | `guard.rs:1628-1631` | epoch.store_lo(0); cached and drained epochs 0 |
| `FL9` | `flush` | `guard.rs:1634-1635` | restored |
| `EX1` | `cleanup` | `guard.rs:1647-1670` | with no tid and a batch, claim_tid; in_reclaim, the pin count, own |
| `ExitSubmit` | `cleanup` | `guard.rs:1689` | submit_at_exit: take_batch, try_retire |
| `ExitSubmit2` | `submit_at_exit` | `guard.rs:1783` | not placed: parked |
| `ExitTake` | `cleanup` | `guard.rs:1698-1700` | the own list taken |
| `ExitFree` | `cleanup` | `guard.rs:1704-1705` | drain_free_list |
| `ExitRound` | `cleanup` | `guard.rs:1679` | EXIT_ROUNDS rounds |
| `ExitParkRest` | `cleanup` | `guard.rs:1712-1713` | the last batch parked |
| `EX6` | `deactivate_slots` | `slot.rs:657` | the reservation's epoch lo 0 |
| `EX7` | `deactivate_slots` | `slot.rs:658-660` | its first exchanged to INVPTR |
| `EX7b` | `deactivate_slots` | `slot.rs:657` | the helper slot's epoch lo 0 |
| `EX7c` | `deactivate_slots` | `slot.rs:658-660` | its first exchanged to INVPTR |
| `EX8` | `cleanup` | `guard.rs:1724-1730` | each captured list traversed |
| `EX9` | `cleanup` | `guard.rs:1731` | the batches released |
| `EX10` | `cleanup` | `guard.rs:1732-1742` | re-armed, parked |
| `EX12` | `cleanup` | `guard.rs:1750-1751` | park_orphans |
| `EX12b` | `cleanup` | `guard.rs:1760` | release_tid |
| `EX13` | `cleanup` | `guard.rs:1762-1771` | restored, the tid unset |
| `SK1` | (model) | | the spin lock's test (ttas_locks only) |
| `SK2` | (model) | | its test-and-set (ttas_locks only) |
| `SK3` | (model) | | the lock taken (ttas_locks only) |
| `AT0` | (model) | | the tid lock (ttas_locks only) |
| `RL0` | (model) | | the tid lock (ttas_locks only) |
| `PK0` | (model) | | the orphan lock (ttas_locks only) |
| `AD0` | (model) | | the orphan lock (ttas_locks only) |
| `TC3` | (model) | | the copies written back (cache_copied, cache_overwritten only) |
| `DN2` | (model) | | the detached list traversed into the cache before the republication (slow_path_frees only) |
| `EX11` | (model) | | the cache drained with the slots inactive (exit_frees_inactive only; a step that does nothing otherwise) |
| `FB2` | (model) | | batch_next read after the destructor ran (read_after_dealloc only) |
| `WR3` | (model) | | the pool's lock released after the retire (pool_lock_held only; a step that does nothing otherwise) |
| `TH2` | (model) | | the program's next operation |
| `THJ` | (model) | | spawned after another thread ended |
| `THR` | (model) | | spawned once a tid was released |
| `THA` | (model) | | goes on once another thread is past n operations |
| `TI2` | (model) | | an idle thread's guard dropped |
| `TI3` | (model) | | an idle thread pins again |

### Configurations

Two threads, two tids and one cell (holding node 1) unless a configuration says otherwise; a
retire submits its batch at every retire (`RETIRE_FREQ` 1), the epoch advances at every second
retire (`EPOCH_FREQ` 2), the cache holds one traversal's batches, two load attempts, two
transition attempts, two exit rounds, the global epoch at most 10 (the state constraint), no
step counts, no recycling. RF, EF, cache and epochs abbreviate `RetireFreq`, `EpochFreq`,
`MaxCache` and `MaxEpoch`; recycle is `Recycle` TRUE.

| configuration | scenario | constants | expected |
|---|---|---|---|
| `RC_rw` | A reader holding what it loaded while a writer replaces and retires it, flushes and exits. | nodes 3 | pass |
| `RC_esc` | Loads that escalate (one attempt) while every retire advances the epoch; the escalated drop transitions. | nodes 3, EF 1, load attempts 1 | pass |
| `RC_slow` | Pins with one fast attempt take the slow path while retires and flushes advance the epoch and help. | nodes 3, EF 1, pin attempts 1 | pass |
| `RC_two_loads` | A section loading three times across retires and epoch advances; nothing cached past one traversal. | nodes 5, cache 0 | pass |
| `RC_lu` | A writer loading unprotected under its own exclusion, a reader loading protected. | nodes 3 | pass |
| `RC_era` | A reader pinned early loads a value born later, which the writer retires: the load raises the reservation. | nodes 7, EF 1 | pass |
| `RC_drain` | One thread: retires advance the epoch, a load raises the reservation, the next pin traverses. | threads 1, tids 1, nodes 3 | pass |
| `RC_flush_esc` | A drop run by flush after its epoch advance escalates its load; flush ends that reservation. | threads 1, tids 1, nodes 3, load attempts 1 | pass |
| `RC_esc_drop` | An escalated drop's transition frees the cache; a drop in it retires into the own slot and pins. | threads 1, tids 1, nodes 8, EF 1, cache 0, load attempts 1 | pass |
| `RC_flush_dtor` | A drop run inside flush reads a cell another thread replaces and retires. | cells 2, nodes 4 | pass |
| `RC_exit_dtor` | A drop run inside a thread's exit reads a cell another thread replaces and retires. | cells 2, nodes 5 | pass |
| `RC_exit_raw` | A drop an exit runs reads a value born after the exiting thread's last transition, which another thread retires. | cells 2, nodes 9 | pass |
| `RC_exit_tid` | A drop an exit runs reads a cell while another thread flushes; a third thread, spawned once a tid is released, takes the exiting thread's over and reads a value the second thread replaces and retires. | threads 3, cells 3, nodes 11, RF 3 | pass |
| `RC_exit_chain` | An exit whose drops retire in a chain: two rounds, the rest parked. | threads 1, tids 1, nodes 5, EF 4 | pass |
| `RC_orphan` | An exit that cannot place its batch parks it on its tid; a flush adopts it. | nodes 3 | pass |
| `RC_flush_orphan` | A thread that never pinned flushes twice at any moment while another exits with a batch it cannot place (parked on its tid); a flush after the park claims a tid and adopts it. | threads 3, tids 3, nodes 2, steps counted yes | pass |
| `RC_unpinned_retire` | Threads that never pin retire one value each; one flushes and exits, the other just exits, while a third holds a reservation: each claims a tid and submits. | threads 3, tids 3, nodes 3, RF 2 | pass |
| `RC_help_dtor` | A retire on a batch and epoch boundary helps a slow path; the help's drain runs a drop that retires. | nodes 6, EF 1, cache 0, pin attempts 1 | pass |
| `RC_reenter` | A cached drop that retires, freed by a transition while another thread's pin, its epoch moved by retires, takes the slow path. | nodes 9, EF 1, cache 0 | pass |
| `RC_reenter_rt` | The same, the cache freed by a retire's help of the slow path. | nodes 9, EF 1, cache 0 | pass |
| `RC_reentrant` | A retire outside any guard frees its batch at once; the drop it runs pins, transitions, loads and drops its guard. | threads 1, tids 1, nodes 3 | pass |
| `RC_slow_dtor` | A slow path detaching its list while a helper hands it over; a cached drop reads a cell, replaces it and retires what it read. | cells 2, nodes 8, RF 2, cache 0, pin attempts 1 | pass |
| `RC_hand_over` | A slow-path hand-over racing a retire into the pending thread's slot. | threads 3, tids 3, nodes 4, pin attempts 1, steps counted yes | pass |
| `RC_help_follows` | A pinner whose every transition takes the slow path, advancing the epoch between its pins, helped from its second request on by another thread's flush. | nodes 6, RF 6, EF 1, pin attempts 1, epochs 8, steps counted yes | pass |
| `RC_live` | Weak fairness for every thread: every program ends. | nodes 3 | pass |
| `RC_live_drain` | One thread that keeps pinning after its retires advanced the epoch and a load raised its reservation: every retired node is eventually released. | threads 1, tids 1, nodes 3 | pass |
| `RC_live_stall` | Only thread 2 is scheduled fairly; thread 1 may stop for good at any step of its exit (a tid release, a park): thread 2's first pin, load, retire and flush end. | nodes 4 | pass |
| `RC_live_orphan` | Weak fairness for every thread; a thread that never pinned flushes once after another exited with a batch it could not place: every parked batch is eventually adopted. | threads 3, tids 3, nodes 2 | pass |
| `RC_live_unpinned_flush` | Weak fairness; one thread retires a value without pinning, flushes, then keeps pinning and unpinning without exiting: the value is eventually freed. | threads 1, tids 1, nodes 2, RF 2 | pass |
| `RC_wf_pin` | Step counts: pins with one fast attempt against a thread that helps and advances the epoch at every flush. | nodes 1, pin attempts 1, epochs 8, steps counted yes | pass |
| `RC_wf_load` | Step counts: loads against a writer that advances the epoch at every retire. | nodes 4, EF 1, load attempts 3, epochs 8, steps counted yes | pass |
| `RC_wf_mix` | Step counts of every operation in the slow-path scenario. | nodes 3, EF 1, pin attempts 1, steps counted yes | pass |
| `RC_wf_exit` | Step counts of exits and flushes running drops. | cells 2, nodes 5, steps counted yes | pass |
| `RC_wf_unpinned_exit` | Step counts: a thread that never pinned retires one value and exits while another pins and unpins: its exit claims a tid and submits. | nodes 2, RF 2, steps counted yes | pass |
| `RC_wf_unpinned_flush` | Step counts: a thread that never pinned retires one value, flushes and exits while another pins and unpins: its flush claims a tid and submits. | nodes 2, RF 2, steps counted yes | pass |
| `RC_mut_drain_published` | drain_published: an outermost pin skips when the global epoch equals the epoch its slot publishes, which a protected load raised. | threads 1, tids 1, nodes 3 | `PinDrains` broken |
| `RC_mut_drain_published_live` | drain_published, as a lasso: a thread that keeps pinning never traverses the list its own retires filled. | threads 1, tids 1, nodes 3 | `DrainLive` broken |
| `RC_mut_escalated_drop_unnested` | escalated_drop_unnested: the escalated drop's transition runs with the pin count 0 and the cache copied out and written back, so a drop's own transition inside it loses what it traversed. | threads 1, tids 1, nodes 8, EF 1, cache 0, load attempts 1 | `NoLoss` broken |
| `RC_mut_flush_keeps_unconditional` | flush_keeps_unconditional: flush returns with the unconditional reservation a drop it ran published. | threads 1, tids 1, nodes 3, load attempts 1 | `EscalationBounded` broken |
| `RC_mut_flush_deactivates` | flush_deactivates: flush deactivates its slot while the drops it runs load. | cells 2, nodes 4 | `NoUseAfterFree` broken |
| `RC_mut_exit_frees_inactive` | exit_frees_inactive: an exit deactivates its slots, then frees what they held, running drops that load unprotected. | cells 2, nodes 5 | `NoUseAfterFree` broken |
| `RC_mut_tid_released_early` | tid_released_early: an exit releases its tid with its slots, before the drops it runs publish into the slot the next owner took. | threads 3, cells 3, nodes 11, RF 3 | `NoUseAfterFree` broken |
| `RC_mut_cache_copied` | cache_copied: a full cache is freed from a copy while its cell still holds it, so a traversal re-entered from a drop frees it again. | nodes 9, EF 1, cache 0 | `NoDoubleFree` broken |
| `RC_mut_help_before_submit` | help_before_submit: a retire helps and advances the epoch before its batch step, which then finalizes the batch its cells hold after nested retires emptied them, with no check. | nodes 9, EF 1, cache 0 | `NoNullDeref` broken |
| `RC_mut_ttas_locks` | ttas_locks: tids and orphans change hands under spin locks; a thread stopped holding one stops every first pin. | nodes 4 | `Thread2Ends` broken |
| `RC_mut_exit_loop` | exit_loop: an exit repeats its rounds until no batch is left, as long as the drops it runs keep retiring. | threads 1, tids 1, nodes 5, EF 4 | `LoopBounds` broken |
| `RC_mut_exit_handle_unreachable` | exit_handle_unreachable: a drop an exit runs finds no handle: its pin pins nothing and its load checks no epoch. | cells 2, nodes 9 | `NoUseAfterFree` broken |
| `RC_mut_slow_path_frees` | slow_path_frees: a slow path frees the full cache at its traversals, the detached list's before the republication, running drops while its slot is closed to new batches: a batch a drop retires skips the slot. | cells 2, nodes 8, RF 2, cache 0, pin attempts 1 | `NoUseAfterFree` broken |
| `RC_mut_detach_unclosed` | detach_unclosed: a detach retries its compare-exchange of the list without closing the era first, so new retires keep failing it. | threads 3, tids 3, nodes 4, pin attempts 1 | `DetachNotStarved` broken |
| `RC_mut_help_follows_next_request` | help_follows_next_request: a helper's loop goes on while the pending thread has any request open, its compare-exchange expecting the request read last, so it runs through the epoch advances of the pending thread's later requests. | nodes 6, RF 6, EF 1, pin attempts 1, epochs 8, steps counted yes | `LoopBounds` broken |
| `RC_find_help_torn_request` | A helper that read a pinner's first request, (INVPTR, 0), while the pinner goes through later cycles: its check of the request can read a later request's INVPTR with the 0 of that request's self-completion; the era's seqno ends its loop. | nodes 5, RF 5, EF 1, pin attempts 1, epochs 8, steps counted yes | pass |
| `RC_mut_help_no_seqno_check` | help_no_seqno_check: a helper goes on while its check reads the request it started with, without the era's seqno, so a torn read of a later request keeps it passing through the pinner's later cycles. | nodes 5, RF 5, EF 1, pin attempts 1, epochs 8, steps counted yes | `LoopBounds` broken |
| `RC_mut_stale_birth` | stale_birth: a thread that advances the epoch keeps stamping its allocations with the epoch it cached before. | threads 1, tids 1, nodes 3, EF 1 | `BirthFresh` broken |
| `RC_mut_flush_keeps_reservation` | flush_keeps_reservation: flush with no guard live ends only an escalated section, leaving the reservation at the epoch it published. | threads 1, tids 1, nodes 3, load attempts 1 | `FlushReleases` broken |
| `RC_mut_flush_needs_tid` | flush_needs_tid: flush does nothing on a thread with no tid, so a thread that never pinned never adopts what an exit parked. | threads 3, tids 3, nodes 2 | `OrphansAdopted` broken |
| `RC_mut_flush_skips_batch` | flush_skips_batch: flush on a thread with no tid ignores its own batch while nothing is parked, so a thread that flushes and lives on never frees what it retired without pinning. | threads 1, tids 1, nodes 2, RF 2 | `RetiredFreed` broken |
| `RC_mut_exit_skips_batch` | exit_skips_batch: the exit of a thread with no tid does nothing, so what a thread retired without pinning and never flushed is never submitted. | nodes 2, RF 2 | `NoLoss` broken |
| `RC_mut_load_traverses` | load_traverses: a protected load that sees the epoch move traverses the slot list instead of only raising the reservation, releasing what the section loaded first. | nodes 5, cache 0 | `NoUseAfterFree` broken |
| `RC_mut_no_era_check` | no_era_check: a protected load does not compare the global epoch. | nodes 7, EF 1 | `NoUseAfterFree` broken |
| `RC_mut_no_help` | no_help: an epoch advance helps no slow path first. | nodes 1, pin attempts 1, epochs 8, steps counted yes | `LoopBounds` broken |
| `RC_mut_no_escalate` | no_escalate: a protected load retries until the epoch settles. | nodes 4, EF 1, load attempts 3, epochs 8, steps counted yes | `WaitFree` broken |
| `RC_wit_free` | a node is freed. | nodes 3 | `NoFreeW` broken |
| `RC_wit_held_retired` | a section holds a node another thread retired. | nodes 3 | `NoHeldRetiredW` broken |
| `RC_wit_escalate` | a load escalates. | nodes 3, EF 1, load attempts 1 | `NoEscalateW` broken |
| `RC_wit_slow` | a pin takes the slow path. | nodes 3, EF 1, pin attempts 1 | `NoSlowW` broken |
| `RC_wit_helped` | a helper completes another thread's slow path. | nodes 3, EF 1, pin attempts 1 | `NoHelpedW` broken |
| `RC_wit_merge` | a batch that cannot be placed goes back to the accumulating one. | nodes 3 | `NoMergeW` broken |
| `RC_wit_park` | an exit parks a batch on its tid. | nodes 3 | `NoParkW` broken |
| `RC_wit_adopt` | a flush adopts a parked batch. | nodes 3 | `NoAdoptW` broken |
| `RC_wit_flush_claim` | a flush on a thread with no tid claims one. | threads 3, tids 3, nodes 2 | `NoFlushClaimW` broken |
| `RC_wit_flush_batch_claim` | a flush on a thread with no tid claims one for its own batch. | nodes 2, RF 2 | `NoFlushClaimW` broken |
| `RC_wit_exit_claim` | an exit on a thread with no tid claims one. | nodes 2, RF 2 | `NoExitClaimW` broken |
| `RC_wit_recycle` | a thread takes a released tid over. | threads 3, cells 3, nodes 11, RF 3 | `NoRecycleW` broken |
| `RC_wit_dtor_held_retired` | a drop holds a node another thread retired. | cells 2, nodes 4 | `NoDtorHeldRetiredW` broken |
| `RC_wit_cache_free` | a traversal frees the full cache first. | threads 1, tids 1, nodes 8, EF 1, cache 0, load attempts 1 | `NoCacheFreeW` broken |
| `RC_wit_second_round` | an exit's second round submits what its first round's drops retired. | threads 1, tids 1, nodes 5, EF 4 | `NoSecondRoundW` broken |
| `RC_wit_closed_skip` | a scan skips a slot whose era a detach closed. | threads 3, tids 3, nodes 4, pin attempts 1 | `NoClosedSkipW` broken |
| `RC_wit_helper_detach` | a helper detaches the pending thread's list. | threads 3, tids 3, nodes 4, pin attempts 1 | `NoHelperDetachW` broken |
| `RC_wit_undo` | an insert finds its slot deactivated and takes its node back. | cells 2, nodes 5 | `NoUndoW` broken |
| `RC_wit_broken_link` | a traversal takes a node before its inserter links it, and the inserter traverses what it displaced. | nodes 5, cache 0 | `NoBrokenLinkW` broken |
| `RC_wit_reentrant_transition` | a drop pins outermost and transitions inside a retire. | threads 1, tids 1, nodes 3 | `NoReentrantTransitionW` broken |
| `RC_recycle` | A reader holding what it loaded while a writer replaces and retires it and flushes between its writes, so later writes take freed nodes back from the pool while the reader loads again. | nodes 4, recycle | pass |
| `RC_recycle_dtor` | Node 1 retired with a fresh node in one batch, the fresh node freed first; node 1's drop, in the same walk, reads cell 2 and replaces it with the node just freed, taken back from the pool, while thread 2 replaces and reads cell 2. | cells 2, nodes 6, recycle | pass |
| `RC_recycle_stale` | `RC_recycle` with stale_reuse: the recycler skips `RetiredNode::new`, so a node goes out again with the header and birth epoch kovan left on it. Every invariant but `BirthFresh`, which checks the epochs `RetiredNode::new` stamps (a stale reuse stamps none). | nodes 4, recycle | pass |
| `RC_recycle_dtor_stale` | `RC_recycle_dtor` with stale_reuse: the node a drop takes back from the walk that freed it keeps the header it had in that batch. Every invariant but `BirthFresh`. | cells 2, nodes 6, recycle | pass |
| `RC_recycle_stale_link_next` | `RC_recycle` with stale_reuse_link_next: no `RetiredNode::new`, and the pool links its nodes through the header's first word (`next`), which the reuse keeps. Every invariant but `BirthFresh`. | nodes 4, recycle | pass |
| `RC_recycle_stale_lag` | stale_reuse on a lagging thread: thread 1 pins at the first epoch and waits while thread 2's flushes advance the epoch and free a node it stamped later into the pool; thread 1 takes that node back with a write and flushes while thread 2 loads the cell. Every invariant but `BirthFresh`. | nodes 5, recycle | pass |
| `RC_mut_reuse_retired` | reuse_retired: the recycler takes a node still in a retirement batch, its destructor not yet run. | nodes 4, recycle | `NoUseAfterFree` broken |
| `RC_mut_read_after_dealloc` | read_after_dealloc: the reclamation walk reads a node's batch_next after its destructor handed the node to the pool. | nodes 4, recycle | `NoUseAfterFree` broken |
| `RC_mut_stale_link_birth` | stale_reuse_link_birth: no `RetiredNode::new`, and the pool links its nodes through the word of `birth_epoch`, so a reused node goes out with a pointer for its birth epoch. | nodes 4, recycle | `NoUseAfterFree` broken |
| `RC_mut_pool_lock_held` | pool_lock_held: a recycler holds its pool's lock from a write's take until the retire of the old value returns; that retire frees the value's batch at once, and the destructor, on the same thread, waits for the lock. | threads 1, tids 1, nodes 3, recycle | deadlock |
| `RC_mut_cache_ahead` | cache_ahead, the programs of `RC_two_loads`: the reader's raise caches the epoch it read and leaves its slot's word as it was. | as `RC_two_loads` | `CacheBelowPublished` broken |
| `RC_mut_early_free` | early_free, the programs of `RC_exit_tid`: three pinned threads, so a batch goes into two slot lists, freed one traversal early. | as `RC_exit_tid` | `ListsHoldNoFreed` broken |
| `RC_mut_help_hands_pointer` | help_hands_pointer, the programs of `RC_find_help_torn_request`: the helper's result carries a pointer. | as `RC_find_help_torn_request` | `WellFormed` broken |
| `RC_mut_drain_published_term` | drain_published as in `RC_mut_drain_published_live`, every thread scheduled fairly, checked against `Termination` with the safety properties beside it. | as `RC_mut_drain_published_live` | `Termination` broken |
| `RC_wit_reuse` | a section holds a node in a later incarnation than its first. | nodes 4, recycle | `NoHeldReusedW` broken |
| `RC_wit_dtor_reuse` | a drop, run inside a reclamation walk, takes a node from the pool. | cells 2, nodes 6, recycle | `NoDtorReuseW` broken |
| `RC_wit_stale_reuse` | a recycled node is about to go out with a birth epoch older than the one `RetiredNode::new` would stamp. | nodes 4, recycle | `NoStaleReuseW` broken |
| `RC_wit_stale_later` | a recycled node is about to go out with a birth epoch later than the one `RetiredNode::new` would stamp on the recycling thread. | nodes 5, recycle | `NoStaleLaterW` broken |
| `RC_wf_recycle` | Step counts with recycling: a reader in two guards while a writer replaces cell 1 three times and flushes between, taking back freed nodes. | nodes 4, recycle, steps counted yes | pass |
| `RC_wf_recycle_dtor` | Step counts with reuse inside a walk: node 1's drop takes back the node the same walk freed a step before. | cells 2, nodes 6, recycle, steps counted yes | pass |
| `RC_wit_wf_reuse` | in `RC_wf_recycle`'s setting, a section holds a node in a later incarnation. | nodes 4, recycle, steps counted yes | `NoHeldReusedW` broken |
| `RC_wit_wf_dtor_reuse` | in `RC_wf_recycle_dtor`'s setting, a drop inside a walk takes a node from the pool. | cells 2, nodes 6, recycle, steps counted yes | `NoDtorReuseW` broken |

### Findings

The model found one defect in the code it was built against, fixed on this branch:

- **A helper loop that outlived the request it helps** (`RC_mut_help_no_seqno_check`, 2,351,551
  states; `RC_find_help_torn_request` passes the same scenario with the fix). `help_thread` went on
  to another pass while its check read the request it started with, `(INVPTR, seqno)`, the request's
  two words read one at a time, the low one first. A self-completion stores `(0, 0)`, and a thread's
  first request is `(INVPTR, 0)`: a check whose low word is a later request's `INVPTR` and whose
  high word is that request's self-completion 0 reads `(INVPTR, 0)` (an answer's epoch equal to the
  request's seqno pairs the same way). A helper that read a thread's first request so went on
  through the thread's later cycles, one more pass for every epoch advance between them, past T + 2
  (five passes with T = 2 in the counterexample): bounded by the other thread's progress, not by T.
  Safety was not at stake, the helper's answer expecting a request no later cycle makes. Fix:
  another pass only while the era's seqno is still the request's (one word, which a cycle leaves at
  seqno + 2 and never brings back). The unit test
  `help_ends_with_its_cycle_across_a_torn_request_read` holds the helper between the two halves of
  its check and forces the torn read: without the seqno check the helper passes more than T + 2
  times, with it once.

On the code before the slow path's detach (the list hand-over of `take_over_list`), the first
compare-exchange of the hand-over epoch loop could also fail on a torn read (the low word read
before the pending thread's compare-exchange of the era, the high one after the slot closed), a case
the comment beside the loop did not name; the bound of two held, the compare-exchange returning the
word atomically. The detach closes the era before the helper reads it, so the only change while the
sequence number is odd is now the pending thread's republication, which the comment names.

The defects this branch fixed, each put back by a mutation:

- **A pin that skips its drain** (`RC_mut_drain_published`, 54 states;
  `RC_mut_drain_published_live`, a lasso). 0.1.21's outermost pin skipped when the global epoch
  equalled the epoch its slot published, which a protected load raises: a thread whose retires
  advanced the epoch and whose load raised the reservation in the same section never traversed its
  list. Fix: compare with `drained_epoch`, the epoch of the last traversal.
- **A drop's transition inside an escalated drop's** (`RC_mut_escalated_drop_unnested`, 201 states).
  0.1.21's escalated guard drop transitioned with the pin count at 0, so a drop freed in that
  transition pinned outermost and transitioned inside it, and the outer traversal's copy of the
  cache, written back after, lost what the inner one put there. Fix: the transition runs with the
  count at 1, and every traversal takes the cache out of its cell before freeing it
  (`traverse_into_cache`). The lost traversal needs a drop's traversal inside another traversal's
  free; with the count kept at 1 that happens only in a help run by a retire outside any guard,
  which no configuration here reaches, so this mutation puts the two defects back together.
- **A flush that keeps the unconditional reservation** (`RC_mut_flush_keeps_unconditional`, 79
  states): a drop run by flush escalated its load, and flush returned with the reservation above
  every epoch. Fix: flush ends such a section.
- **A flush that deactivates its slot** (`RC_mut_flush_deactivates`, 24,304 states): 0.1.21's flush
  set its list to INVPTR while the drops it ran loaded, so a retire elsewhere skipped the slot and
  freed what a drop held. Fix: the slot stays active through flush.
- **An exit that frees with its slots inactive** (`RC_mut_exit_frees_inactive`, 73,607 states), and
  **a tid released before the exit's drops** (`RC_mut_tid_released_early`, 1,544,254 states): the
  drop's raise, made after the release, lowered the epoch the tid's next owner published, and a
  batch of later values skipped the slot. Fix: the exit runs every drop while its slot is active and
  releases the tid last.
- **A cache freed from a copy** (`RC_mut_cache_copied`, 9,766 states): a full cache freed from a
  copy while its cell still held it was freed again by a traversal a drop re-entered. Fix: the cache
  leaves its cell before it is freed (`traverse_into_cache`).
- **A batch finalized after nested retires emptied it** (`RC_mut_help_before_submit`, 12,986
  states): a retire helped and advanced the epoch before its batch step, and retires nested in the
  help emptied the batch the step then finalized. Fix: the batch step comes first.
- **Tids and orphans under spin locks** (`RC_mut_ttas_locks`, a lasso): a thread stopped holding the
  lock stopped every first pin, flush and exit. Fix: a bitmap of released tids and a chain parked on
  each tid, both lock-free.
- **An exit that runs as long as others retire** (`RC_mut_exit_loop`, 77 states): an exit repeated
  its rounds until no batch was left. Fix: two rounds, the rest parked.
- **A drop at exit with no handle** (`RC_mut_exit_handle_unreachable`, 3,752 states): on builds
  whose handle is a destructed thread-local, a drop the exit ran found none, so its load was
  unprotected. Fix: the exiting handle stays reachable.
- **A slow path that frees while its slot is closed** (`RC_mut_slow_path_frees`, 4,979 states): a
  slow path freed the full cache at its traversals, while a helper's detach held its slot closed to
  new batches, so a batch a drop retired skipped the slot. Fix: the slow path's traversals only move
  batches onto the cache, drained once the slot is republished.
- **A list hand-over that new retires keep failing** (`RC_mut_detach_unclosed`, 225,566 states): the
  take of the list retried its compare-exchange of the slot without closing the slot to new batches
  first, so every new retire into it could fail the take again. Fix: the slot closes first (now the
  era's sequence number goes odd), and scans skip a closed slot.
- **A helper that follows the next request** (`RC_mut_help_follows_next_request`, 820,966 states): a
  helper went on while the pending thread had any request open, through the epoch advances of its
  later requests. Fix: the loop ends once the request it read changes (and, since a torn read can
  hide that change, once the era's seqno moves on: `RC_mut_help_no_seqno_check` above).
- **A stale birth stamp** (`RC_mut_stale_birth`, 29 states): a thread that advanced the epoch kept
  stamping allocations with an older epoch, so what it retired waited for slots stalled below the
  epoch it had made. Fix: an advance refreshes the stamp.
- **A flush that keeps the reservation** (`RC_mut_flush_keeps_reservation`, 81 states): flush with
  no guard live left the reservation at the epoch it published, so every batch retired afterwards
  waited for a thread that may idle. Fix: flush takes the list once more and publishes epoch 0.
- **A flush that never adopts on a thread with no tid** (`RC_mut_flush_needs_tid`, a lasso, 14,404
  states): flush returned at once on a thread that had never pinned, so what exited threads parked
  could stay parked for good. Fix: such a flush claims a tid while some tid holds orphans,
  then adopts. Found by reading the code after the model was built, not by the model: its `Flush`
  returned at the same point, and `NoLoss` counts a parked batch as kept. See the next section.
- **A batch left behind by a thread with no tid** (`RC_mut_exit_skips_batch`, 296 states;
  `RC_mut_flush_skips_batch`, a lasso, 22 states): on a thread that had never pinned,
  flush still returned at once while nothing was parked, with values in its own batch, and the
  exit did nothing, so what such a thread retired was never submitted and never freed. Fix: such
  a flush, and such an exit, claim a tid and submit the batch. Found by reading the code while
  fixing the defect above; the model had the same returns, and `NoLoss` sees the exit half once a
  configuration has a thread retire without pinning and exit. See "Values retired by a thread
  that never pinned".

Four more mutations take a mechanism out to show the properties depend on it: `load_traverses` (a
load that traverses the list instead of raising the reservation releases what the section loaded
first), `no_era_check`, `no_help` and `no_escalate`.

What the model shows about recycling (`retire_reclaimable`, this branch), including where a claim
in `reclaim.rs` stops holding, is under "Recycling nodes" above ("What TLC found").

The model this replaces, `model_chk/Kovan.tla`, modelled a former per-slot reference-count design
without epochs; its use-after-free check was not part of the next-state relation, so it never ran,
its liveness property was defined but checked by no configuration, and its eight-thread
configuration did not finish.

### A flush on a thread that never pinned

The story, with three threads:

1. Thread C pins and holds its reservation (it neither flushes nor exits yet).
2. Thread A pins, replaces a value and retires the old one, then exits. A's batch holds that one
   value, and C's slot is eligible for it. A batch is placed only when it has more nodes than there
   are eligible slots, so this one cannot be placed. A's exit parks it on A's tid (the tid's orphan
   word; `orphaned` counts the tids whose word holds a chain), releases the tid and ends. The value
   now waits for a `flush()` to adopt it.
3. Thread B never pins: it only drops `Atom`s, say, and each drop calls `flush()`. B has no tid.

Before the fix, B's `flush()` returned at its first line, because B had no tid, and never adopted
A's batch. Unless a thread that has a tid flushes later, the value stays parked for good: its
destructor never runs and its memory is never freed. The model had the same return, at `FL1` of
`Flush`, and no property caught it: `NoLoss` looks at the state once every thread has exited, and
it counts a batch parked on a tid as kept, not lost.

After the fix, B's `flush()` first loads `orphaned`. It is not zero, so B claims a tid (the claim
a first pin makes), adopts the chain parked on one tid and submits it with its own batch. While C
still holds its reservation the adopted batch cannot be placed yet and stays in B's batch, to be
submitted again at B's next flush or at its exit; once C has exited, no slot is eligible and the
value is freed. B keeps the tid until its own exit, which releases it. When `orphaned` is zero,
B's `flush()` returns at once, as before, and claims nothing.

The two unit tests in `kovan/src/guard/tests.rs` tell the same story in code.
`flush_without_a_tid_adopts_orphans`: four threads A park one value each while C is pinned, C
exits, then B flushes at most once per tid handed out; the test checks that every value is freed,
that B's flush claimed a tid and that B's exit released it. On the code before the fix it failed
in 20 runs of 20, all four values still parked. `flush_without_a_tid_or_orphans_claims_none`: with
nothing parked anywhere, B's two flushes leave B without a tid and take none (no tid handed out
anew, no released one taken back).

What changed in the model (each line of `FL1` carries the same explanation as a comment):

- `FL1` is the start of `flush()`, one step: it reads the thread's own tid, `in_reclaim` and pin
  count, and, on a thread with no tid, the shared count `orphaned`.
- The test for returning at once: when the thread has no tid and nothing is parked anywhere, or,
  as before, when the flush runs inside a destructor that a reclamation of this thread is running.
  Before the fix the test was `tid[self] = NoTid \/ inr[self]`: no tid, always return. (The next
  section adds a third condition, that the thread's own batch is empty.)
- `call AllocTid(); goto FL2` with no guard live, `call AllocTid(); goto FL3` with one: a thread
  with no tid that gets past that test claims a tid, then goes on as any flush does: its own slot
  list (`FL2`, only with no guard live), the adoption (`FL3`), the submission, the epoch advance,
  the drain and the release of the reservation. A thread that already has a tid is unchanged.
- `FlushCtl`, the step bound of a flush, also counts the claim (`TidCtl`): `WaitFree` holds a flush
  that claims a tid to a bound that includes the claim's steps.
- `MutFlushNeedsTid`, the mutation `flush_needs_tid`, puts the old test back.

The property `OrphansAdopted` (`MC_Reclaim.tla`) is `<>[](\A i \in Tids : orw[i] = NULL)`, read
"eventually, and from then on always, no tid's orphan word holds a chain". It is a liveness
property: TLC checks it on every schedule in which a thread that can take a step does take it in
the end (weak fairness), on a scenario that runs a flush on a thread with no tid after any park.

The configurations, and what each one catches:

- `RC_flush_orphan` (must pass). Thread 1 exits while thread 2 holds a reservation, so its
  one-value batch is parked; thread 3, with no tid, flushes twice at any moment, then exits. TLC
  tries every interleaving and checks the safety invariants with the step counts on: no value freed
  while a guard holds it or freed twice, no batch lost once every thread has exited (`NoLoss`),
  every loop and every operation within its bound (`LoopBounds`, `WaitFree`), the flush that claims
  a tid included. A change to that path that broke one of them in this scenario would fail here.
- `RC_wit_flush_claim` (must be broken). It asserts that no flush ever claims a tid, on the same
  scenario. TLC breaking it shows that the scenario reaches the new branch, so the pass of
  `RC_flush_orphan` covers that branch instead of passing because it never ran.
- `RC_live_orphan` (must pass). Thread 1 parks as above; thread 3, with no tid, waits until thread
  1 has ended, then flushes once. TLC checks `OrphansAdopted` on every fair schedule: wherever
  thread 1 parked its batch, the batch is adopted in the end. It checks the adoption, not the free:
  thread 3 stops after its flush without exiting, and while thread 2 holds its reservation the
  adopted batch stays in thread 3's batch.
- `RC_mut_flush_needs_tid` (must be broken). The scenario of `RC_live_orphan` with the old `FL1`
  put back. TLC finds a schedule in which thread 1 parks its batch, thread 3's flush returns
  without adopting, every thread ends and the batch stays parked forever: `OrphansAdopted` broken.
  `NoLoss` cannot see this: with the old `FL1`, the scenario of `RC_flush_orphan` still satisfies
  `NoLoss` (54,832 distinct states, no error, in a run made for this note, not a configuration of
  `EXPECTED.txt`), since a parked batch counts as kept.

What these checks do not cover: TLC checks these scenarios (three threads, one cell, one value
retired) exhaustively, not every program; and no operation runs after a thread's exit in the
model, so a flush made by a thread-local destructor after the exit (`exit_pending`) is not checked.

### Values retired by a thread that never pinned

The story, with one thread:

1. Thread A never pins. It only retires values: it drops `Removed` values another thread handed
   it, say, and each such drop retires the value without a pin. The values go into A's
   accumulating batch. A has no tid: a pin claims one, and so do a flush or an exit that needs one
   and the epoch advance at every 128th retire; a retire submits the batch only every 64th time.
2. A retires 10 values, then either calls `flush()` and exits, or just exits.

Before the fix, A's `flush()` returned at once: A had no tid and nothing was parked anywhere (the
fix above looked at parked batches, not at A's own). A's exit did nothing either, on a thread with
no tid. A's batch went down with A's handle: never submitted, so its values' destructors never ran
and their memory was never freed, whatever other threads did afterwards. The model had the same
two returns, at `FL1` of `Flush` and `EX1` of `Exit`, and no configuration had a thread retire
without pinning and then flush or exit.

After the fix, A's `flush()` also goes on when A's own batch holds a value: it claims a tid (the
claim a first pin makes, and only while A's exit is still to run, `exit_pending`) and submits the
batch as any flush does. A's exit, finding no tid and a batch that holds a value, claims a tid
(`claim_tid`, the claim without the nightly sentinel the exit runs inside) and runs the exit every
thread runs: submit, park what cannot be placed, release the tid last. On the nightly build the
exit runs only from a sentinel a thread registers when it claims a tid; a thread with no tid that
starts a batch now registers it in `enqueue_node`, so its exit runs. When A retired nothing, its
flush and its exit return at once, as before, and claim nothing.

The integration test `kovan/tests/unpinned_retire.rs` tells the same story in code. An integration
test builds the library as users get it: in the unit-test build a test-only hook claims a tid
whenever a submission inserts a value into a slot, so a thread that went through one would have a
tid and hide the defect. `unpinned_thread_that_flushes_frees_what_it_retired`: A retires 10 values,
flushes and exits; the test checks that all 10 are freed right after the flush, and still after
another thread's 100 rounds of pin and flush. `unpinned_thread_that_exits_frees_what_it_retired`: A
retires 10 values and exits; the test checks that all 10 are freed after those rounds. On the code
before the fix both failed in 20 runs of 20, all 10 values still live. With the flush half of the
fix alone the exit case passed and the flush case failed (its values still live after the flush);
with the exit half alone the flush case passed and the exit case failed. Both pass with the fix, on
the nightly build too, where removing the sentinel registration makes the exit case fail.

What changed in the model (each new or changed line carries the same explanation as a comment):

- `FL1`: the test for returning at once also requires that the thread's own batch is empty
  (`bfst[self] = NULL`). A thread with no tid and a value in its batch claims a tid
  (`call AllocTid()`) and goes on as any flush, which submits the batch at `FL4`.
- `EX1`: a thread with no tid returns at once only when its batch is empty. With a value in it,
  the thread claims a tid (`call AllocTid(); goto EX1`) and comes back to `EX1`, which then runs
  the exit of a thread that has a tid.
- `ExitCtl`, the step bound of an exit, also counts that claim and the second pass of `EX1`.
- Two mutations put back the two returns as the fix above left them, one at a time:
  `flush_skips_batch` (`MutFlushSkipsBatch`: flush with no tid returns while nothing is parked,
  whatever its batch holds) and `exit_skips_batch` (`MutExitSkipsBatch`: the exit of a thread with
  no tid does nothing).
- `NoExitClaimW`, a witness: no exit ever claims a tid. With `NoFlushClaimW` it shows that a
  configuration reaches the claim it is meant to check.

Two properties, one per half. The exit half: `NoLoss`, unchanged: when every thread has exited,
every retired value is freed or in a batch parked on a tid. A value left in the batch of a thread
that has exited is neither, so `NoLoss` sees it; it missed this defect only because no
configuration had a thread retire without pinning and then exit. The flush half: `NoLoss` cannot
see it, because it looks only at the end, once every thread has exited, and the exit alone then
submits the batch; what the flush half adds is that the values are freed while the thread still
lives. So the new `RetiredFreed` (`MC_Reclaim.tla`), `<>[](\A n \in Nodes : nst[n] # "retired")`:
"eventually, and from then on always, no value is in the state retired", every retired value
freed. It is a liveness property, checked on a thread that retires, flushes and then lives on
without exiting.

The configurations, and what each one catches:

- `RC_unpinned_retire` (must pass). With a batch of two (`RetireFreq` 2), one retire does not
  submit. Thread 1 retires one value without pinning, flushes and exits; thread 2 retires one and
  exits; thread 3 pins, unpins and exits, so until it exits a one-value batch cannot be placed and
  is kept or parked. TLC tries every interleaving and checks the safety invariants on each,
  `NoLoss` among them, with the flush of thread 1 and the exit of thread 2 each claiming a tid.
  Steps are not counted here: with the step counts on, this scenario reached 19,998,315 distinct
  states, still growing, when a 600-second limit stopped TLC. The two configurations below count
  them, one claim at a time.
- `RC_wf_unpinned_exit` (must pass, steps counted). Thread 1 retires one value and exits; thread 2
  pins, unpins and exits. Thread 1's exit finds no tid and a value in its batch, claims a tid and
  runs the normal exit (and parks the value while thread 2 holds its reservation). TLC checks the
  safety invariants on every interleaving, `NoLoss` and `WaitFree` among them: the exit, its claim
  included, stays within its step bound.
- `RC_wf_unpinned_flush` (must pass, steps counted). Thread 1 retires one value, flushes and
  exits; thread 2 pins, unpins and exits. Nothing is parked before thread 1's flush, so its claim
  is made for its own batch. The same invariants, `WaitFree` holding the flush and its claim to
  the flush's bound.
- `RC_wit_exit_claim` and `RC_wit_flush_batch_claim` (must be broken). Witnesses on those two
  scenarios: "no exit claims a tid" and "no flush claims a tid". TLC breaking them shows that each
  scenario reaches its claim, so the two passes above cover it rather than passing because it
  never ran.
- `RC_mut_exit_skips_batch` (must be broken). The scenario of `RC_wf_unpinned_exit` with only the
  exit's old return put back (the flush half stays, but thread 1 never flushes). In the
  counterexample TLC finds, thread 1's exit returns at once, both threads end, and the value is
  still in thread 1's batch, neither freed nor parked: `NoLoss` broken.
- `RC_live_unpinned_flush` (must pass) and `RC_mut_flush_skips_batch` (must be broken). One thread
  retires one value, flushes, then pins and unpins forever without exiting, so only its flush can
  submit the value. TLC checks `RetiredFreed` on every fair schedule: with the fix the flush claims
  a tid and frees the value; with only the flush's old return put back (the exit half stays, but
  the thread never exits), TLC finds the lasso in which the flush returns at once and the value
  stays in the batch forever.

What these checks do not cover: TLC checks these scenarios (one or two threads beside the three of
`RC_unpinned_retire`, one value retired per thread that never pins) exhaustively, not every
program. The nightly sentinel registration is not modelled (the model's exit always runs).

### TLC results

The run recorded in `reclaim/tlc-run.txt` (12 workers for a passing configuration, one for a
violation, on a 36-core machine shared with other heavy work, other TLC runs among it): 103 of 103
configurations match `EXPECTED.txt`, in 2518 s of wall time. The largest passing ones are
`RC_recycle_dtor` (10,055,217 distinct states, 177 s), `RC_recycle_dtor_stale` (9,977,235
distinct states, 217 s), `RC_wf_mix` (8,363,530 distinct states, 143 s), `RC_unpinned_retire`
(8,173,791 distinct states, 152 s), `RC_hand_over` (5,601,019 distinct states, 112 s),
`RC_find_help_torn_request` (3,371,877 distinct states, 59 s), `RC_two_loads` (2,790,043 distinct
states, 49 s) and `RC_flush_orphan` (2,197,419 distinct states, 47 s); the longest runs that break
a property, on one worker, are `RC_mut_help_no_seqno_check` (2,351,551 distinct states, 268 s) and
`RC_mut_tid_released_early` (1,544,254 distinct states, 260 s). The four mutations that give
`CacheBelowPublished`, `ListsHoldNoFreed`, `WellFormed` and `Termination` one of their own each
stop within seconds: `RC_mut_cache_ahead` (4,703 distinct states), `RC_mut_early_free` (16,954),
`RC_mut_help_hands_pointer` (27,719) and `RC_mut_drain_published_term` (57). TLC checks a temporal
property on the part of the state space found so far, at intervals during the search, so where it
stops on a broken one, and the state count it reports, can differ between runs
(`RC_mut_ttas_locks`, for one).

## What the map models check

- Every operation keeps an abstract map (`abs`), changed at the operation's linearization point,
  and a history of its changes (`hist`). A lookup's, a remove's and a conditional insert's answer
  must be a value the key held at some moment of the call (`SeenDuring`), and `insert_if_absent`
  and `get_or_insert` must answer `None` (their own value) exactly when their own write inserted.
  A broken check sets `err`, and each kind has a named invariant:
  - `Exactness`: a conditional insert answers exactly;
  - `CondExact`: a conditional write (`remove_if`, `replace_if`, `compute`) runs its closure
    once, on the value the key holds at the step that writes what the closure decided (or at the
    step that keeps it), and an answer of absence is linearizable;
  - `Linearizable`: lookups and removes answer linearizably;
  - `NoUseAfterFree`: reclamation is modelled as kovan provides it, a pointer loaded from a link
    (a slot) protects its node (entry) for the rest of the operation when the node was not retired
    at the load; reading one not protected so is a use after free;
  - `WalkExact`: a walk yields every key present for its whole length once, nothing never
    present, and (for the hopscotch map) no key twice, (for the chained map) no key more often
    than its lives during the walk.
- `AbsIsContent`: the abstract map is what a lookup of the current table finds (no entry lost,
  none resurrected); `NoDuplicate`: no key has two entries a lookup can find.
- `RetiredUnreachable`: no node or entry is retired while a table in use can reach it.
- `OldFrozen` (chained) and `OldHeld` (hopscotch): a replaced table admits no write.
- `CountExact`: at rest the count is the number of entries.
- `NoLeak`: when every thread is done, every allocated node or entry is freed, retired, or held by
  a table in use.
- `Termination` (the `*_live` configurations, under weak fairness of every thread): every
  operation ends. `ReaderEnds` (the `*_live_reader` and `*_live_walker` configurations, where
  only the reader is scheduled fairly and every writer may stop anywhere): a lookup or a walk
  ends without waiting for any writer.
- Witnesses (`*_wit_*`): each asserts a case never happens, so TLC's counterexample proves the
  passing configurations reach it and are not vacuous.
- Every property above has at least one mutation (`*_mut_*`) that breaks it, so none of them is a
  check that could never fail. Where TLC stops at another property first, a configuration runs the
  mutation against that property alone (named after the mutation and the property, such as
  `HS_mut_unguarded_remove_count`) and expects that property to break. The properties no 0.1.20
  rule breaks get a mutation of their own: an insert that does not look for its key's entry first
  (`insert_skips_lookup`, `NoDuplicate`), a remove that unlinks a node and never retires it
  (`unlink_no_retire`, chained `NoLeak`), a lookup that waits for a writer guard
  (`get_waits_for_guard`, hopscotch `ReaderEnds`) and an insert that never releases its guard
  (`insert_keeps_guard`, hopscotch `Termination`). `NoError` is the conjunction of the named
  checks above, each of which a mutation breaks.

The hash of a key is the key itself (the identity hasher of the tests), so a configuration places
every key where the case needs it. The worker threads run fixed programs (`MC_*.tla`), a resizer
thread runs a program of grows, shrinks and clears, and the hopscotch writers also grow the table
themselves when an insert finds no room.

## The chained map (`chained/ChainedMap.tla`)

### What is transcribed from the code

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

### Configurations

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

### Findings: the kovan-map 0.1.20 defects each mutation puts back

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

### TLC results

The run recorded in `chained/tlc-run.txt` (8 workers for a passing configuration, one for a
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

## The hopscotch map (`hopscotch/HopscotchMap.tla`)

### What is transcribed from the code

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

### The shrink threshold, in plain words

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

#### The work of failed shrinks, with several threads

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

### Configurations

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

### Findings

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

### TLC results

The run recorded in `hopscotch/tlc-run.txt` (8 workers for a passing configuration, one for a
violation, beside other work on a 36-core machine): 69 of 69 configurations match `EXPECTED.txt`,
in 192 s of TLC time; the largest passing ones are `HS_big_disp` (4,588,001 distinct states, 65 s)
and `HS_big_cond` (1,444,974, 22 s). The 61 configurations recorded before the mutations for
`NoDuplicate`, `ReaderEnds` and `Termination` and the five single-property runs were added reach
exactly the states (generated and distinct) and give exactly the results they gave before: a
mutation hook changes nothing while its mutation is off. In the same way, every configuration that
passed before the reserved word reaches exactly the states it reached before, the 47 that predate
the shrink threshold exactly those recorded before it was modelled, and the 57 that predate the
work history (`work`) exactly those recorded before it was added (earlier versions of
`hopscotch/tlc-run.txt`).

## The segment queue (`segqueue/SegQueue.tla`)

### What is transcribed from the code

`kovan_queue::SegQueue` (`kovan-queue/src/seg_queue.rs`) at the grain of its atomic steps: the
two claim words and the two segment pointers, the cells (state and value), each segment's
successor link, and kovan's reclamation of the segments the head retires.

- A push pins, loads the tail pointer, claims a cell with a fetch-add of the tail word, walks to
  the claimed segment (and moves a lagging tail pointer on), writes its value and publishes it
  with the compare-and-swap of the cell from `EMPTY` to `FULL`; a failed compare-and-swap (a pop
  took the cell out of play) claims again. A claim past the end of a segment links the successor
  with the value in its first cell (or meets the successor another push linked), moves the tail
  word to the successor's second cell, then the tail pointer.
- A pop reads the head word, then the tail word, and classifies the two (`classify`). On `Empty`
  it answers `None`; otherwise it pins, loads the head pointer, and either claims a cell with a
  fetch-add of the head word and swaps it to `TAKEN` (a `FULL` cell is its value, an `EMPTY` one
  is taken out of play), or, on `Drained`, finds the successor (none: the queue is empty), moves
  the head word to it and walks the head pointer forward, moving the tail pointer off each
  segment first; the winner of the head pointer's compare-and-swap retires the segment.
- `try_pop` reads the words the same way, pinned after a first look, and claims only the cell
  the head word names, by a compare-and-swap of the head word, after reading the cell `FULL`; it
  answers `Busy` for an `EMPTY` one.
- kovan's reclamation is what the reclamation family proves of it: a retired segment is freed
  once every operation that was in progress when it was retired has ended.

What is left out or folded, and why it changes nothing:

- Segment ids are counted without wrapping and a segment's successor has the next id (the code
  allocates it so, and links one successor per segment). The code's ids wrap at `2^44` and its
  positions at `2^49`; `proofs/lean/Kovan/SegQueue.lean` proves its `classify`, `behind`,
  `position` and `len` give the answers counted without wrapping while the two words stay as
  close as `Words` below keeps them.
- Segments have `SEG` cells (2 in every configuration, 32 in the code): a segment fills, links
  and drains within a few operations, so every move of the words and pointers is reached.
- A pop's `PATIENCE` re-reads of an `EMPTY` cell are folded into its swap, which may come at any
  moment after the claim, so every number of re-reads is covered.
- A walk of pointers forward (`locate`, `catch_up_tail`) is one step, as the pointers only move
  forward; the tail word's and the head word's compare-and-swap loops are one step each, the
  step of the compare-and-swap that succeeds.
- A step that touches only the thread's own state (a loop counter, a pin, an unpin, a check of
  its own answer) is folded into the shared step next to it, which no other thread can tell
  apart. `try_pop`'s read of a `FULL` cell and its claim by the head word's compare-and-swap are
  one step: the cell stays `FULL` until its claimer takes it, and that claim moves the word.
- `len` and `is_empty` are not operations of the model: `len` is two loads and the arithmetic
  the Lean proof covers, and `is_empty` answers with the view and `drained` that `pop` uses.

### Properties

Every check is made at the step it is about and recorded in `errs`; each invariant says one kind
of check never failed.

- `NoUseAfterFree`: no step reads or writes a segment kovan freed.
- `NoUnlinkedClaim`: a claimed cell's segment is always reachable from the pointer loaded before
  the claim, so the code's `debug_assert!` path is never taken.
- `NoBound`: no push met the configuration's bound on segments, so the configurations are
  complete for their operations.
- `EmptySound`: at the step that tells a pop or a `try_pop` the queue is empty, every push that
  has returned has its cell claimed by a pop.
- `BusyMeansClaimed`: `try_pop` answers `Busy` only for a cell a push claimed and has not written.
- `UniqueTake`: no value is taken twice.
- `RealTimeOrder`: a push writes its value behind every push that returned before it began (so
  one producer's values sit in the order it pushed them).
- `PopOrder`: a pop takes a value behind every value taken before it began (so each consumer
  takes values in queue order).
- `NoLoss`: when every thread is done, every value pushed was taken or still sits in its cell at
  or past the head, where a later pop takes it.
- `Words`: the head word is at most one segment ahead of the tail word, and only once the tail
  word passed its segment's end. It is the hypothesis of the Lean theorem `classifyCode_word`;
  no mutation here breaks it, because the head word moves to a segment only from a `Drained`
  view, which already needs the tail word past the end.
- `Termination` (under `FairSpec`, every thread's steps taken fairly): every operation ends. A
  push that loses its cell to a pop claims the next one, and within a segment of `SEG` cells it
  claims past the end and links the successor with its value, completing in that step, so a push
  and a pop cannot keep taking each other's cells forever.

### Mutations and witnesses

Each mutation puts back one wrong rule and lists its property first, the others after it, so
that TLC, which stops at the first state that breaks any of them, names the one the mutation is
for. Every property but `Words` (see above) has one. One is checked against its property alone:
the stale store of `SQ_mut_store_tail_advance` also moves the tail word back under a tail pointer
that went ahead, which breaks `NoUnlinkedClaim` in a shorter trace than the one that breaks
`RealTimeOrder`.

| configuration | the wrong rule | expected |
|---|---|---|
| `SQ_mut_scan_pop` | the earlier design's pop: take the first `FULL` cell of the head segment, passing over one still being written | `PopOrder` broken |
| `SQ_mut_no_poison` | a pop that finds its cell `EMPTY` moves on without taking it out of play, so the late push writes where no pop claims again | `NoLoss` broken |
| `SQ_mut_retire_before_tail` | the head's walk retires a segment without first moving the tail pointer off it | `NoUseAfterFree` broken |
| `SQ_mut_busy_without_view` | `try_pop` answers `Busy` without telling from the words that a push claimed the cell | `BusyMeansClaimed` broken |
| `SQ_mut_tail_before_head` | a pop reads the tail word before the head word | `EmptySound` broken |
| `SQ_mut_link_then_retry` | a push that linked the successor with its value goes on pushing the value | `UniqueTake` broken |
| `SQ_mut_store_tail_advance` | `advance_tail_word` checks the word's segment, then stores the successor's word instead of a compare-and-swap; three producers | `RealTimeOrder` broken |
| `SQ_mut_load_after_claim` | a push loads the tail pointer after its claim | `NoUnlinkedClaim` broken |
| `SQ_mut_retry_same_cell` | a push whose cell was taken out of play retries its compare-and-swap on that cell, forever | `Termination` broken |

The witnesses each claim a case never happens, so their counterexamples show the passing
configurations reach it: a push links a successor (`SQ_wit_link`, `NoLinkW`), a pop takes an
unwritten cell out of play (`SQ_wit_poison`, `NoPoisonW`), `try_pop` answers `Busy`
(`SQ_wit_busy`, `NoBusyW`), kovan frees a retired segment (`SQ_wit_free`, `NoFreeW`), a pop
answers that the queue is empty (`SQ_wit_empty`, `NoEmptyAnswerW`), the head word moves one
segment ahead of the tail word (`SQ_wit_head_ahead`, `NoHeadAheadW`), and, with two segments
only, a push meets the bound `NoBound` checks (`SQ_wit_bound`).

### Configurations

| configuration | threads | operations |
|---|---|---|
| `SQ_mpsc` | two producers, one consumer | two pushes each, four pops |
| `SQ_mpmc` | one producer, two consumers | three pushes, two pops each |
| `SQ_try` | two producers, one consumer | two pushes each, four `try_pop`s |
| `SQ_push3` | three producers | two pushes each |
| `SQ_live` | two producers, one consumer, `FairSpec` | one push each, two pops; checks `Termination` |

Segments of two cells and room for five segments (six in `SQ_push3`) in every one.

### Code map

| label | function | code | step |
|---|---|---|---|
| `PU1` | `push` | `seg_queue.rs:475`, `seg_queue.rs:481` | the pin, then the tail pointer loaded |
| `PU2` | `push` | `seg_queue.rs:481` | the tail pointer loaded again for a new claim |
| `PU3` | `push` | `seg_queue.rs:482` | the tail word's fetch-add |
| `PU4` | `push`, `locate` | `seg_queue.rs:485-492` | the walk to the claimed segment |
| `PU4a` | `push`, `catch_up_tail` | `seg_queue.rs:493-496` | the lagging tail pointer moved on |
| `PU4b` | `push` | `seg_queue.rs:502-514` | the value written, the cell's compare-and-swap |
| `PU5` | `push`, `locate` | `seg_queue.rs:517-523` | segment full: the walk to it (or the word moved after a pointer a pop moved), its `next` loaded |
| `PU6` | `push` | `seg_queue.rs:524-555` | the successor linked with the value in its first cell, or the one linked met |
| `PU7` | `advance_tail_word` | `seg_queue.rs:590-602` | the tail word moved to the successor's second cell |
| `PU8` | `advance_tail` | `seg_queue.rs:575-584` | the tail pointer's compare-and-swap, or `catch_up_tail`; a push that linked returns |
| `PO1`, `PO2` | `pop`, `view` | `seg_queue.rs:710-713`, `seg_queue.rs:748` | the head word, then the tail word, classified |
| `PO3` | `pop` | `seg_queue.rs:714-716` | the pin, the head pointer loaded |
| `PO4` | `pop` | `seg_queue.rs:725` | the head word's fetch-add |
| `PO5` | `pop`, `locate`, `take` | `seg_queue.rs:729-744` | the walk to the cell, the swap to `TAKEN` |
| `PO6` | `pop` | `seg_queue.rs:719-723` | after `drained`: empty, or look again |
| `DR1` | `drained` | `seg_queue.rs:639-649` | the walk to the head word's segment, its `next` loaded |
| `DR2` | `drained` | `seg_queue.rs:650-661` | the head word moved to the successor's first cell |
| `CH1`, `CH2` | `catch_up_head` | `seg_queue.rs:671-682` | the head pointer loaded, its id against the head word, its `next` loaded |
| `CH3` | `catch_up_head` | `seg_queue.rs:683-688` | the tail pointer moved off the segment |
| `CH4` | `catch_up_head` | `seg_queue.rs:689-700` | the head pointer's compare-and-swap; its winner retires the segment |
| `TP1`, `TP2` | `try_pop`, `view` | `seg_queue.rs:771-773` | the first look at the two words |
| `TP3`, `TP4`, `TP5` | `try_pop` | `seg_queue.rs:774-786` | the pin, the head pointer, the two words again |
| `TP6` | `try_pop`, `locate` | `seg_queue.rs:788-804` | the cell read; `Busy`, or the head word's compare-and-swap |
| `TP7` | `try_pop` | `seg_queue.rs:782-786` | after `drained` |
| `TP8` | `try_pop`, `take` | `seg_queue.rs:805-807` | the swap to `TAKEN` |
| `RC1` | kovan | `retire_reclaimable`, the guard's drop | a retired segment freed once its holders' operations ended |

### TLC results

The run recorded in `segqueue/tlc-run.txt` (4 workers for a passing configuration, one for a
violation, at the lowest priority on a 36-core machine shared with other heavy work): 21 of 21
configurations match `EXPECTED.txt`, in 1514 s of wall time. The passing ones are `SQ_mpmc`
(72,271,075 distinct states, 788 s), `SQ_mpsc` (34,816,107, 383 s), `SQ_push3` (2,399,746, 31 s),
`SQ_try` (345,338, 7 s) and `SQ_live` (50,897, 6 s, with `Termination`). The longest runs that
break a property, on one worker, are `SQ_mut_store_tail_advance` (3,842,091 distinct states,
151 s) and `SQ_mut_link_then_retry` (2,149,256, 74 s). The counterexample of
`SQ_mut_store_tail_advance` needs three producers: one links the next segment, checks the tail
word's segment and is descheduled before its store; a second claims a cell of that next segment
and is descheduled before writing it; the third links the segment after that and returns, and
the stale store then moves the tail word back over the unwritten cell, where the third's next
push writes its value, ahead of the one it pushed before.

## The magazine cache (`magazine/Magazine.tla`)

### What is transcribed from the code

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
  protocol is the slab family below.
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

### Properties

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

### Mutations and witnesses

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

### Configurations

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

### Code map

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

### TLC results

The run recorded in `magazine/tlc-run.txt` (4 workers for a passing configuration, one for a
violation, at the lowest priority on a 36-core machine shared with other heavy work): 20 of 20
configurations match `EXPECTED.txt`, in 1659 s of wall time. The passing ones are `MG_race`
(47,740,142 distinct states, 996 s), `MG_trade` (5,261,842, 104 s), `MG_two` (2,161,034, 56 s),
`MG_live` (1,563,754, 100 s, with `Termination`) and `MG_rounds` (504,070, 13 s). The longest runs
that break a property, on one worker, are `MG_mut_stale_ticket` (1,021,716 distinct states, 194 s)
and `MG_mut_pop_no_claim` (1,243,628, 163 s). `MG_mut_stale_ticket` breaks a liveness property,
which TLC checks at intervals on the part of the state space explored so far, so the count it stops
at varies from run to run (CI's run of the same model stopped at 1,304,519).

## The slab layer (`slab/Slab.tla`)

### What is transcribed from the code

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

### Properties

- `NoUseAfterFree`: no thread touches a freed chunk or a freed inbox.
- `BlockOnce`: every carved block of a live chunk is in exactly one place: a thread, a releaser
  giving it back, the inbox, the owner's collected blocks, the chunk's free list, or counted back
  into an orphaned chunk.
- `BlocksOfFreed`: no block of a freed chunk is held, given back, in the inbox or collected.
- `UsedRight`: while the owner runs, a chunk's count of blocks out is right.
- `CountsRight`: once written at the exit, a chunk's count is its blocks out, and positive.
- `NoLeak`: once every thread is done, every chunk and the inbox are freed.
- `Termination`, under fairness.

### Mutations and witnesses

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

### Configurations

| configuration | releasers | owner operations, chunks |
|---|---|---|
| `SL_two` | two | nine, three chunks |
| `SL_one` | one | eight, three chunks |
| `SL_deep` | two | ten, four chunks |
| `SL_live` | two, fair | three; `Termination` |

Chunks of two blocks in every one.

### Code map

| label | function | code | step |
|---|---|---|---|
| `OW1` (alloc) | `SlabClass::alloc` | `slab.rs:237-269` | a free-list block, a carved one, or the chunk off the partial list |
| `OW1` (drain), `OW2`, `OW2s` | `SlabClass::drain_inbox`, `settle` | `slab.rs:291-331` | the inbox swapped, each block to its chunk, an empty chunk freed or kept |
| `OW1` (new chunk) | `SlabClass::new_chunk` | `slab.rs:334-377` | a chunk made, its inbox reference taken |
| `OW1` (give back), `OW3` | `SlabClass::release_own`, `settle` | `slab.rs:277-312` | a block back to its own chunk |
| `RR1`, `RR2` | `release_remote` | `slab.rs:492-516` | the chunk's inbox, the inbox word, the push's CAS |
| `RR4` | `count_down`, `free_chunk`, `release_inbox` | `slab.rs:477-483`, `slab.rs:193-206`, `slab.rs:106-112` | the count-down; the last frees the chunk and maybe the inbox |
| `EX1`-`EX6` | `SlabClass::orphan` | `slab.rs:432-469` | the drain, the counts, the close and its count-downs, the owner's reference |

### TLC results

The run recorded in `slab/tlc-run.txt` (the magazine run's settings): 15 of 15 configurations
match `EXPECTED.txt`, in 40 s of wall time. The passing ones are `SL_deep` (1,885,607 distinct
states, 19 s), `SL_two` (390,403, 6 s), `SL_one` (23,197, 2 s) and `SL_live` (535, 1 s, with
`Termination`). Every mutation breaks its property within 1,393 distinct states
(`SL_mut_free_one_early`) and two seconds.
