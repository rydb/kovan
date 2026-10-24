/-!
# Flush and exit on a thread that never pinned

This file checks two decisions of kovan's reclamation, the start of `flush()`
(`Handle::flush` in `kovan/src/guard.rs`) and the start of a thread's exit (`Handle::cleanup`),
and what follows from them: a thread that never pinned loses nothing it retired, and the
batches exited threads parked are adopted.

## The story in plain words

A thread gets a thread ID (a tid) the first time it pins. A thread that never pins has none,
yet it can still retire values (dropping a `Removed` value retires it without a pin), and they
wait in its batch. A thread that exits with a batch it cannot place parks it on its tid, as a
chain that a later `flush()` adopts.

Before the fixes, `flush()` returned at once on a thread with no tid, and so did the exit: the
values in such a thread's batch were never submitted, and a chain parked by an exited thread
was never adopted by a thread that only flushes. Now `flush()` on a thread with no tid claims a
tid, as a first pin does, when its own batch holds a value or some tid holds a parked chain,
and otherwise still returns at once, claiming nothing. The exit of a thread with no tid whose
batch holds a value claims a tid and runs the exit every thread runs.

This file proves:

1. exactly when `flush()` and the exit each return at once, claim a tid, or run with the tid
   the thread has (`flush_returns_iff`, `flush_claims_iff`, `exit_returns_iff`, ...);
2. over any sequence of retires, flushes, pins and an exit on one thread, with any outcome for
   every submission, every value the thread retired or adopted is submitted or parked once it
   has exited (`leak_free`, `retired_is_kept`); with the exit as it was before the fix, a
   thread that retires one value and exits keeps it nowhere (`old_exit_loses`);
3. a thread that keeps flushing, with a tid or not, adopts every chain parked on any of
   `maxThreads` tids within `maxThreads` flushes (`adopted_within_max_threads`), so within
   `maxThreads + 1` (`adopted_within`).

## What the model leaves out

One thread, one operation at a time: the TLA+ model in `proofs/tla/reclaim` checks how the
threads interleave. Whether a submission can place its batch depends on the slots of other
threads, so it is a free choice made with each submission; a submission that places the
batch counts its values as submitted, whether they then go into slots or are freed at once.
The exit's two rounds and the parking of what its own slot held are left out: here the exit
submits its batch once and parks it if it cannot place it. The count of tids holding chains is
exact here (in the code it can lag a park for a moment). The runs of 2 and 3 are calls made
outside any reclamation (`in_reclaim` false) and before the exit has run.
-/

namespace Kovan.FlushExit

/-! ## The two decisions -/

/-- How `flush()` or the exit starts. -/
inductive Start where
  /-- It returns at once and does nothing. -/
  | returns
  /-- It claims a tid first (`alloc_tid`, the claim a first pin makes), then runs. -/
  | claims
  /-- It runs with the tid the thread already has. -/
  | runs
  deriving DecidableEq, Repr

/-- The start of `Handle::flush`: the test on the tid, then the test on `in_reclaim`.
* `hasTid`: the thread holds a tid (`self.tid.get().is_some()`);
* `batchEmpty`: its batch holds no value (`self.batch_first.get().is_null()`);
* `orphansParked`: some tid holds a parked chain (`orphans_parked()`);
* `exitPending`: the thread's exit is still to run (`exit_pending()`);
* `inReclaim`: this flush runs inside a destructor that a reclamation of the thread is
  running (`self.in_reclaim.get()`).

Examples: a thread with no tid, an empty batch and nothing parked anywhere returns
(`flushStart false true false true false = .returns`); the same thread with one value in its
batch claims (`flushStart false false false true false = .claims`). -/
def flushStart (hasTid batchEmpty orphansParked exitPending inReclaim : Bool) : Start :=
  if !hasTid && ((batchEmpty && !orphansParked) || !exitPending) then .returns
  else if inReclaim then .returns
  else if !hasTid then .claims
  else .runs

/-- The start of `Handle::cleanup`, the exit: with no tid and a value in its batch it claims a
tid (`claim_tid`), then it runs if the thread has a tid; a thread with no tid and an empty
batch has nothing to leave, and returns.
Examples: `exitStart false true = .returns`; `exitStart false false = .claims`. -/
def exitStart (hasTid batchEmpty : Bool) : Start :=
  if !hasTid && batchEmpty then .returns
  else if !hasTid then .claims
  else .runs

/-- The start of the exit before the fix: with no tid it returned at once, whatever its batch
held. Example: `exitStartOld false false = .returns`, a batch left behind. -/
def exitStartOld (hasTid _batchEmpty : Bool) : Start :=
  if !hasTid then .returns else .runs

/-- `flush()` returns at once exactly when the thread has no tid and either has nothing to
submit or adopt or its exit has already run, or when it runs inside a reclamation. -/
theorem flush_returns_iff (hasTid batchEmpty orphansParked exitPending inReclaim : Bool) :
    flushStart hasTid batchEmpty orphansParked exitPending inReclaim = .returns ↔
      (hasTid = false ∧ ((batchEmpty = true ∧ orphansParked = false) ∨ exitPending = false))
        ∨ inReclaim = true := by
  -- Every input is true or false: Lean checks the 32 combinations one by one.
  cases hasTid <;> cases batchEmpty <;> cases orphansParked <;> cases exitPending <;>
    cases inReclaim <;> decide

/-- `flush()` claims a tid exactly when the thread has none, runs outside any reclamation
before its exit, and has a value in its batch or finds a chain parked. -/
theorem flush_claims_iff (hasTid batchEmpty orphansParked exitPending inReclaim : Bool) :
    flushStart hasTid batchEmpty orphansParked exitPending inReclaim = .claims ↔
      hasTid = false ∧ inReclaim = false ∧ exitPending = true ∧
        (batchEmpty = false ∨ orphansParked = true) := by
  -- The same 32 combinations.
  cases hasTid <;> cases batchEmpty <;> cases orphansParked <;> cases exitPending <;>
    cases inReclaim <;> decide

/-- `flush()` runs with the tid it has exactly when the thread has one and runs outside any
reclamation: for such a thread the fixes change nothing. -/
theorem flush_runs_iff (hasTid batchEmpty orphansParked exitPending inReclaim : Bool) :
    flushStart hasTid batchEmpty orphansParked exitPending inReclaim = .runs ↔
      hasTid = true ∧ inReclaim = false := by
  -- The same 32 combinations.
  cases hasTid <;> cases batchEmpty <;> cases orphansParked <;> cases exitPending <;>
    cases inReclaim <;> decide

/-- A flush on a thread with no tid, an empty batch and nothing parked anywhere claims no tid:
it has nothing to do, and a tid it claimed would stay taken until the thread exits. -/
theorem flush_idle_claims_none (exitPending inReclaim : Bool) :
    flushStart false true false exitPending inReclaim = .returns := by
  -- Two inputs left: the four combinations.
  cases exitPending <;> cases inReclaim <;> decide

/-- The exit returns at once exactly when the thread has no tid and nothing in its batch. -/
theorem exit_returns_iff (hasTid batchEmpty : Bool) :
    exitStart hasTid batchEmpty = .returns ↔ hasTid = false ∧ batchEmpty = true := by
  -- The four combinations.
  cases hasTid <;> cases batchEmpty <;> decide

/-- The exit claims a tid exactly when the thread has none and a value in its batch. -/
theorem exit_claims_iff (hasTid batchEmpty : Bool) :
    exitStart hasTid batchEmpty = .claims ↔ hasTid = false ∧ batchEmpty = false := by
  -- The four combinations.
  cases hasTid <;> cases batchEmpty <;> decide

/-- The exit runs with the tid it has exactly when the thread has one: unchanged by the fix. -/
theorem exit_runs_iff (hasTid batchEmpty : Bool) :
    exitStart hasTid batchEmpty = .runs ↔ hasTid = true := by
  -- The four combinations.
  cases hasTid <;> cases batchEmpty <;> decide

/-! ## One thread's run -/

/-- An operation of the thread, with the outcome of the submission it may make: `placed` says
whether `try_retire` could place the batch, a choice the model leaves free.
* `retire v boundary placed`: `retire` of the value `v`; at a batch boundary (`boundary`,
  every 64th retire in the code) the retire submits the batch;
* `flush placed`: `flush()`, called outside any reclamation;
* `pin`: an outermost `pin()`, which claims a tid when the thread has none;
* `exit placed`: the thread's exit. -/
inductive Op where
  | retire (v : Nat) (boundary placed : Bool)
  | flush (placed : Bool)
  | pin
  | exit (placed : Bool)

/-- What the model keeps of the thread and of the parked chains.
* `hasTid`: the thread holds a tid;
* `batch`: the values in its accumulating batch, not submitted yet;
* `words`: the orphan word of each tid (`ThreadSlots::orphans`): the chain parked on it, or
  `[]`;
* `submitted`: the values of the batches it submitted and placed (or freed at once);
* `parked`: the values its exit parked on its tid;
* `owned`: every value it retired or adopted, a record the code does not keep, kept here for
  the theorems;
* `exited`: its exit has run. -/
structure St where
  hasTid : Bool
  batch : List Nat
  words : List (List Nat)
  submitted : List Nat
  parked : List Nat
  owned : List Nat
  exited : Bool

/-- A thread that has done nothing yet, beside the chains `words` that exited threads parked.
Example: `init [[], [3]]` has no tid, an empty batch, and one chain parked on tid 1. -/
def init (words : List (List Nat)) : St :=
  ⟨false, [], words, [], [], [], false⟩

/-- Whether some tid holds a parked chain: `orphans_parked()` (the code reads a count of such
tids; here the answer is exact). Example: `anyParked [[], [3]] = true`. -/
def anyParked (ws : List (List Nat)) : Bool :=
  ws.any (fun w => !w.isEmpty)

/-- `adopt_orphans`: the chain of the first tid whose word holds one, and the words with that
one emptied; nothing when no word holds a chain.
Example: `adoptOne [[], [3, 4], [5]] = ([3, 4], [[], [], [5]])`. -/
def adoptOne : List (List Nat) → List Nat × List (List Nat)
  | [] => ([], [])
  | [] :: ws => ((adoptOne ws).1, [] :: (adoptOne ws).2)
  | (x :: xs) :: ws => (x :: xs, [] :: ws)

/-- A submission of the values `vals` (`try_retire`): placed, they count as submitted and
leave the batch; not placed, they stay in the batch (`merge_batch`). The result is the new
batch and the new list of submitted values.
Examples: `submit true [1] [] = ([], [1])`; `submit false [1] [] = ([1], [])`. -/
def submit (placed : Bool) (vals submitted : List Nat) : List Nat × List Nat :=
  if placed then ([], vals ++ submitted) else (vals, submitted)

/-- A retire of `v`: the value joins the batch and, at a batch boundary (`boundary`), the
batch is submitted with it. Nothing happens once the thread has exited.
Example: from `init []`, `retireStep _ 7 false false` leaves `[7]` in the batch. -/
def retireStep (s : St) (v : Nat) (boundary placed : Bool) : St :=
  if s.exited then s
  else if boundary then
    { s with batch := (submit placed (v :: s.batch) s.submitted).1,
             submitted := (submit placed (v :: s.batch) s.submitted).2,
             owned := v :: s.owned }
  else { s with batch := v :: s.batch, owned := v :: s.owned }

/-- A flush, called outside any reclamation before the exit: it starts by `flushStart`. Unless
it returns at once, the thread holds a tid from then on (the one it had, or the one it claims),
adopts one chain into its batch and submits the batch. Nothing happens once it has exited.
Example: from `init [[3]]`, a flush whose submission is placed submits `[3]`. -/
def flushStep (s : St) (placed : Bool) : St :=
  if s.exited then s
  else if flushStart s.hasTid s.batch.isEmpty (anyParked s.words) true false = .returns then s
  else
    { s with hasTid := true, words := (adoptOne s.words).2,
             batch := (submit placed ((adoptOne s.words).1 ++ s.batch) s.submitted).1,
             submitted := (submit placed ((adoptOne s.words).1 ++ s.batch) s.submitted).2,
             owned := (adoptOne s.words).1 ++ s.owned }

/-- An outermost pin: it claims a tid if the thread has none. Nothing happens once the thread
has exited. -/
def pinStep (s : St) : St :=
  if s.exited then s else { s with hasTid := true }

/-- The exit, starting by the rule `exitRule` (`exitStart` now, `exitStartOld` before the
fix). Unless it returns at once, it submits the batch, parks it on the thread's tid if it
cannot place it, and releases the tid; either way the thread has exited.
Example: with `exitStart`, a thread with no tid and `[7]` in its batch, whose submission is
not placed, ends with `[7]` parked. -/
def exitStep (exitRule : Bool → Bool → Start) (s : St) (placed : Bool) : St :=
  if s.exited then s
  else if exitRule s.hasTid s.batch.isEmpty = .returns then { s with exited := true }
  else if placed then
    { s with batch := [], submitted := s.batch ++ s.submitted, hasTid := false,
             exited := true }
  else
    { s with batch := [], parked := s.batch ++ s.parked, hasTid := false, exited := true }

/-- What one operation does, the exit starting by the rule `exitRule`. -/
def step (exitRule : Bool → Bool → Start) (s : St) : Op → St
  | .retire v boundary placed => retireStep s v boundary placed
  | .flush placed => flushStep s placed
  | .pin => pinStep s
  | .exit placed => exitStep exitRule s placed

/-- A run: the operations `ops`, one after another, from the state `s`. -/
def run (exitRule : Bool → Bool → Start) (s : St) (ops : List Op) : St :=
  ops.foldl (step exitRule) s

/-- Running `a` then `b` is running `a ++ b`. -/
theorem run_append (exitRule : Bool → Bool → Start) (s : St) (a b : List Op) :
    run exitRule s (a ++ b) = run exitRule (run exitRule s a) b := by
  -- A run is a left fold, and a fold over `a ++ b` folds `a` first.
  simp [run, List.foldl_append]

/-! ## Nothing retired is lost -/

/-- Every value the thread owns is in its batch, submitted, or parked. -/
def Kept (s : St) : Prop :=
  ∀ v, v ∈ s.owned → v ∈ s.batch ∨ v ∈ s.submitted ∨ v ∈ s.parked

/-- The invariant of a run: every owned value is kept, and once the thread has exited its
batch is empty. -/
def Good (s : St) : Prop :=
  Kept s ∧ (s.exited = true → s.batch = [])

/-- A thread that has done nothing yet is good: it owns nothing and has not exited. -/
theorem init_good (words : List (List Nat)) : Good (init words) := by
  -- It owns no value, and `exited` is false.
  constructor
  · intro v hv
    simp [init] at hv
  · intro h
    simp [init] at h

/-- A submission loses nothing: a value in `vals`, already submitted, or parked, ends in the
new batch, among the submitted values, or still parked. -/
theorem submit_keeps (placed : Bool) (vals submitted parked : List Nat) (v : Nat)
    (h : v ∈ vals ∨ v ∈ submitted ∨ v ∈ parked) :
    v ∈ (submit placed vals submitted).1 ∨ v ∈ (submit placed vals submitted).2 ∨
      v ∈ parked := by
  cases placed
  · -- Not placed: nothing moves.
    simpa [submit] using h
  · -- Placed: everything in `vals` is now among the submitted values.
    simpa [submit, or_assoc] using h

/-- Every operation keeps the invariant, with the exit as it is now. -/
theorem step_good (s : St) (op : Op) (h : Good s) : Good (step exitStart s op) := by
  obtain ⟨hk, hx⟩ := h
  cases op with
  | retire v boundary placed =>
    show Good (retireStep s v boundary placed)
    unfold retireStep
    split
    · -- The thread has exited: nothing changes.
      exact ⟨hk, hx⟩
    next hne =>
    split
    · -- A retire at a batch boundary: the new value and the batch are submitted together.
      refine ⟨?_, fun h => absurd h hne⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · -- The value just retired is in the batch handed to the submission.
        exact submit_keeps _ _ _ _ _ (Or.inl (List.mem_cons_self ..))
      · -- An older value was in the batch, submitted or parked: the submission keeps it.
        rcases hk w hw with hb | hs | hp
        · exact submit_keeps _ _ _ _ _ (Or.inl (List.mem_cons_of_mem _ hb))
        · exact submit_keeps _ _ _ _ _ (Or.inr (Or.inl hs))
        · exact submit_keeps _ _ _ _ _ (Or.inr (Or.inr hp))
    · -- A retire inside a batch: the value joins the batch.
      refine ⟨?_, fun h => absurd h hne⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inl (List.mem_cons_self ..)
      · rcases hk w hw with hb | hs | hp
        · exact Or.inl (List.mem_cons_of_mem _ hb)
        · exact Or.inr (Or.inl hs)
        · exact Or.inr (Or.inr hp)
  | flush placed =>
    show Good (flushStep s placed)
    unfold flushStep
    split
    · -- The thread has exited: nothing changes.
      exact ⟨hk, hx⟩
    next hne =>
    split
    · -- The flush returns at once: nothing changes.
      exact ⟨hk, hx⟩
    · -- The flush adopts one chain into its batch and submits the batch.
      refine ⟨?_, fun h => absurd h hne⟩
      intro w hw
      rcases List.mem_append.mp hw with ha | hw
      · -- An adopted value is in the batch handed to the submission.
        exact submit_keeps _ _ _ _ _ (Or.inl (List.mem_append_left _ ha))
      · -- A value owned before was in the batch, submitted or parked.
        rcases hk w hw with hb | hs | hp
        · exact submit_keeps _ _ _ _ _ (Or.inl (List.mem_append_right _ hb))
        · exact submit_keeps _ _ _ _ _ (Or.inr (Or.inl hs))
        · exact submit_keeps _ _ _ _ _ (Or.inr (Or.inr hp))
  | pin =>
    show Good (pinStep s)
    unfold pinStep
    split
    · -- The thread has exited: nothing changes.
      exact ⟨hk, hx⟩
    · -- A pin claims a tid; the values do not move.
      exact ⟨hk, hx⟩
  | exit placed =>
    show Good (exitStep exitStart s placed)
    unfold exitStep
    split
    · -- The thread has exited already: nothing changes.
      exact ⟨hk, hx⟩
    split
    next hr =>
      -- The exit returns at once. It does so only with no tid and an empty batch
      -- (`exit_returns_iff`), so the thread exits with nothing in its batch.
      have hb : s.batch = [] := List.isEmpty_iff.mp ((exit_returns_iff _ _).mp hr).2
      exact ⟨hk, fun _ => hb⟩
    split
    · -- Placed: the whole batch is submitted, and the batch is empty.
      refine ⟨?_, fun _ => rfl⟩
      intro w hw
      rcases hk w hw with hb | hs | hp
      · exact Or.inr (Or.inl (List.mem_append_left _ hb))
      · exact Or.inr (Or.inl (List.mem_append_right _ hs))
      · exact Or.inr (Or.inr hp)
    · -- Not placed: the whole batch is parked on the thread's tid, the batch is empty.
      refine ⟨?_, fun _ => rfl⟩
      intro w hw
      rcases hk w hw with hb | hs | hp
      · exact Or.inr (Or.inr (List.mem_append_left _ hb))
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr (List.mem_append_right _ hp))

/-- A whole run keeps the invariant: by induction, one operation at a time. -/
theorem run_good (ops : List Op) (s : St) (h : Good s) : Good (run exitStart s ops) := by
  induction ops generalizing s with
  | nil =>
    -- No operation: the state is the one we started from.
    exact h
  | cons op ops ih =>
    -- The first operation keeps the invariant, and the rest of the run then does.
    exact ih (step exitStart s op) (step_good s op h)

/-- Leak freedom: once a thread has exited, every value it retired or adopted, over any run
of retires, flushes, pins and its exit, with any outcome for every submission, is submitted
or parked. -/
theorem leak_free (ops : List Op) (words : List (List Nat))
    (hex : (run exitStart (init words) ops).exited = true) (v : Nat)
    (hv : v ∈ (run exitStart (init words) ops).owned) :
    v ∈ (run exitStart (init words) ops).submitted ∨
      v ∈ (run exitStart (init words) ops).parked := by
  -- The invariant holds at the end of the run.
  obtain ⟨hk, hx⟩ := run_good ops (init words) (init_good words)
  rcases hk v hv with hb | hs | hp
  · -- In the batch: impossible, since the thread exited with its batch empty.
    rw [hx hex] at hb
    exact absurd hb (List.not_mem_nil)
  · exact Or.inl hs
  · exact Or.inr hp

/-- An operation never forgets a value the thread owns. -/
theorem step_owned (e : Bool → Bool → Start) (s : St) (op : Op) (v : Nat)
    (h : v ∈ s.owned) : v ∈ (step e s op).owned := by
  -- Every branch keeps `owned` or puts values in front of it.
  cases op with
  | retire w boundary placed =>
    show v ∈ (retireStep s w boundary placed).owned
    unfold retireStep
    split
    · exact h
    split
    · exact List.mem_cons_of_mem _ h
    · exact List.mem_cons_of_mem _ h
  | flush placed =>
    show v ∈ (flushStep s placed).owned
    unfold flushStep
    split
    · exact h
    split
    · exact h
    · exact List.mem_append_right _ h
  | pin =>
    show v ∈ (pinStep s).owned
    unfold pinStep
    split <;> exact h
  | exit placed =>
    show v ∈ (exitStep e s placed).owned
    unfold exitStep
    split
    · exact h
    split
    · exact h
    split <;> exact h

/-- A run never forgets a value the thread owns. -/
theorem run_owned (e : Bool → Bool → Start) (ops : List Op) (s : St) (v : Nat)
    (h : v ∈ s.owned) : v ∈ (run e s ops).owned := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => exact ih (step e s op) (step_owned e s op v h)

/-- A retire made before the exit owns its value. -/
theorem retire_owned (e : Bool → Bool → Start) (s : St) (v : Nat) (boundary placed : Bool)
    (hx : s.exited = false) : v ∈ (step e s (.retire v boundary placed)).owned := by
  -- Both branches of a retire put `v` in front of `owned`.
  show v ∈ (retireStep s v boundary placed).owned
  unfold retireStep
  simp only [hx, Bool.false_eq_true, ↓reduceIte]
  split <;> exact List.mem_cons_self ..

/-- Every value the thread retires before its exit is submitted or parked once it has
exited: a retire of `v` after the operations `pre` (the thread not exited yet) and before the
operations `post` (an exit among them). -/
theorem retired_is_kept (pre post : List Op) (words : List (List Nat)) (v : Nat)
    (boundary placed : Bool) (hpre : (run exitStart (init words) pre).exited = false)
    (hex : (run exitStart (init words) (pre ++ .retire v boundary placed :: post)).exited = true) :
    v ∈ (run exitStart (init words) (pre ++ .retire v boundary placed :: post)).submitted ∨
      v ∈ (run exitStart (init words) (pre ++ .retire v boundary placed :: post)).parked := by
  -- The retire owns `v`, the rest of the run keeps owning it, and owned values are kept.
  apply leak_free _ _ hex
  rw [run_append]
  exact run_owned _ post _ v (retire_owned _ _ v boundary placed hpre)

/-- With the exit as it was before the fix, a thread that retires one value inside a batch
and exits keeps it nowhere: not in a batch, not submitted, not parked. -/
theorem old_exit_loses :
    let s := run exitStartOld (init []) [.retire 7 false false, .exit true]
    s.exited = true ∧ 7 ∈ s.owned ∧ 7 ∉ s.submitted ∧ 7 ∉ s.parked := by
  -- Lean runs the two operations and checks the four facts.
  decide

/-! ## Every parked chain is adopted -/

/-- How many tids hold a parked chain: the count `orphaned` in `slot.rs`.
Example: `holding [[], [3], [4, 5]] = 2`. -/
def holding (ws : List (List Nat)) : Nat :=
  (ws.filter (fun w => !w.isEmpty)).length

/-- No more tids hold a chain than there are tids. -/
theorem holding_le_length (ws : List (List Nat)) : holding ws ≤ ws.length :=
  -- Filtering a list never lengthens it.
  List.length_filter_le _ _

/-- Some tid holds a chain exactly when the count of such tids is not zero. -/
theorem anyParked_iff (ws : List (List Nat)) : anyParked ws = true ↔ holding ws ≠ 0 := by
  induction ws with
  | nil =>
    -- No tid: nothing parked, and the count is zero.
    simp [anyParked, holding]
  | cons w ws ih =>
    -- The first word holds a chain or not; the rest is the induction hypothesis.
    cases w <;> simp_all [anyParked, holding]

/-- An adoption empties one word when some word holds a chain: one tid fewer holds one. -/
theorem adoptOne_holding (ws : List (List Nat)) (h : holding ws ≠ 0) :
    holding (adoptOne ws).2 + 1 = holding ws := by
  induction ws with
  | nil =>
    -- No word at all: the count was zero, against the hypothesis.
    simp [holding] at h
  | cons w ws ih =>
    cases w with
    | nil =>
      -- The first word is empty: the adoption looks further, as the code's pass does.
      simp only [adoptOne, holding, List.filter_cons, List.isEmpty_nil, Bool.not_true,
        Bool.false_eq_true, ite_false] at h ⊢
      exact ih h
    | cons x xs =>
      -- The first word holds a chain: the adoption takes it and leaves the rest.
      simp [adoptOne, holding]

/-- An adoption when no word holds a chain leaves none holding one. -/
theorem adoptOne_holding_zero (ws : List (List Nat)) (h : holding ws = 0) :
    holding (adoptOne ws).2 = 0 := by
  induction ws with
  | nil =>
    -- No word: nothing changes.
    simp [adoptOne, holding]
  | cons w ws ih =>
    cases w with
    | nil =>
      -- An empty first word stays empty; the rest by induction.
      simp only [adoptOne, holding, List.filter_cons, List.isEmpty_nil, Bool.not_true,
        Bool.false_eq_true, ite_false] at h ⊢
      exact ih h
    | cons x xs =>
      -- A first word holding a chain contradicts a zero count.
      simp [holding] at h

/-- A flush, before the exit, takes the count of tids holding a chain down by one, or keeps
it at zero; and the thread has still not exited. On a thread with no tid this rests on the
fix: such a flush returns at once only when nothing is parked (`flush_returns_iff`). -/
theorem flush_holding (e : Bool → Bool → Start) (s : St) (placed : Bool)
    (hx : s.exited = false) :
    holding (step e s (.flush placed)).words = holding s.words - 1 ∧
      (step e s (.flush placed)).exited = false := by
  show holding (flushStep s placed).words = holding s.words - 1 ∧
    (flushStep s placed).exited = false
  unfold flushStep
  simp only [hx, Bool.false_eq_true, ↓reduceIte]
  split
  next hr =>
    -- The flush returned at once: then nothing was parked, so the count is zero.
    have hp : anyParked s.words = false := by
      rcases (flush_returns_iff _ _ _ _ _).mp hr with ⟨_, ⟨_, h⟩ | h⟩ | h
      · exact h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
    have h0 : holding s.words = 0 :=
      Decidable.byContradiction fun hne => by
        -- A nonzero count would mean some chain is parked, against `hp`.
        have h2 := (anyParked_iff s.words).mpr hne
        rw [hp] at h2
        exact absurd h2 (by decide)
    exact ⟨by omega, hx⟩
  · -- The flush adopted: the count goes down by one, or stays zero; it did not exit.
    refine ⟨?_, rfl⟩
    by_cases h0 : holding s.words = 0
    · show holding (adoptOne s.words).2 = holding s.words - 1
      rw [adoptOne_holding_zero _ h0, h0]
    · have h1 := adoptOne_holding _ h0
      show holding (adoptOne s.words).2 = holding s.words - 1
      omega

/-- A run of flushes at least as long as the count of tids holding a chain adopts every chain:
no tid holds one at the end. -/
theorem flushes_adopt (e : Bool → Bool → Start) (ps : List Bool) (s : St)
    (hx : s.exited = false) (hn : holding s.words ≤ ps.length) :
    holding (run e s (ps.map Op.flush)).words = 0 := by
  induction ps generalizing s with
  | nil =>
    -- No flush: the count was at most zero.
    simp at hn
    exact hn
  | cons p ps ih =>
    -- The first flush lowers the count by one (or keeps it zero), the rest by induction.
    obtain ⟨hc, hx'⟩ := flush_holding e s p hx
    apply ih (step e s (.flush p)) hx'
    simp at hn
    omega

/-- A count of zero means every word is empty. -/
theorem holding_zero (ws : List (List Nat)) (h : holding ws = 0) : ∀ w ∈ ws, w = [] := by
  induction ws with
  | nil =>
    -- No word.
    intro w hw
    exact absurd hw List.not_mem_nil
  | cons w ws ih =>
    intro u hu
    cases w with
    | nil =>
      -- The first word is empty; the others by induction.
      simp only [holding, List.filter_cons, List.isEmpty_nil, Bool.not_true,
        Bool.false_eq_true, ite_false] at h
      rcases List.mem_cons.mp hu with rfl | hu
      · rfl
      · exact ih h u hu
    | cons x xs =>
      -- A first word holding a chain contradicts a zero count.
      simp [holding] at h

/-- Every chain parked on any of `maxThreads` tids is adopted within `maxThreads` flushes of a
thread that has not exited, whether it holds a tid or not and whatever each submission's
outcome: afterwards every orphan word is empty. -/
theorem adopted_within_max_threads (maxThreads : Nat) (s : St) (ps : List Bool)
    (hx : s.exited = false) (hw : s.words.length = maxThreads)
    (hp : maxThreads ≤ ps.length) :
    ∀ w ∈ (run exitStart s (ps.map Op.flush)).words, w = [] := by
  -- At most `maxThreads` tids hold a chain, no more than the flushes run.
  apply holding_zero
  apply flushes_adopt _ ps s hx
  have := holding_le_length s.words
  omega

/-- The bound as the code's tests use it: `maxThreads + 1` flushes adopt every chain parked on
any of `maxThreads` tids (one flush more than `adopted_within_max_threads` needs). -/
theorem adopted_within (maxThreads : Nat) (s : St) (ps : List Bool)
    (hx : s.exited = false) (hw : s.words.length = maxThreads)
    (hp : ps.length = maxThreads + 1) :
    ∀ w ∈ (run exitStart s (ps.map Op.flush)).words, w = [] :=
  -- `maxThreads + 1` flushes are at least `maxThreads`.
  adopted_within_max_threads maxThreads s ps hx hw (by omega)

end Kovan.FlushExit
