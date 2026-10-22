import Kovan.HopscotchShrink

/-!
# The shrink threshold when several threads share the map

`Kovan/HopscotchShrink.lean` proves the work bound of failed shrinks for one thread doing one
operation at a time. This file drops that simplification and proves the bound that holds when
many threads use the map at once.

## The story in plain words

A remove asks for a shrink in one step (the end of `unlink_held`, in
`kovan-map/src/hopscotch.rs`) and the shrink copies the map in a later step (`try_resize`, in
`kovan-map/src/hopscotch/resize.rs`), after the remove has let go of its bucket. Other threads
keep working in between, and two things can happen there.

1. Inserts land. The remove left 3 entries and asked, but by the time the copy runs the map
   holds 4. The copy clones 4 entries, more than the threshold looked at.
2. Other removes ask too. Two threads each remove an entry and each asks for a shrink before
   either shrink has run. The first shrink fails and writes its threshold, but the second
   thread asked before that threshold existed, so its shrink runs anyway and fails at about the
   same count. One failed copy can be repeated once by every thread that had already asked.

So the single-thread rule "each failed shrink is at fewer than half the entries of the one
before" is not true across threads (the example `two_threads_fail_at_the_same_count` below
shows two failures at the same count). What stays true is a rule for each thread on its own:

- every thread's failed copies add up to less than twice its first failed copy plus twice the
  number of inserts that came after that first one (`thread_failed_copies_lt_after`; with all
  the inserts of the run, `thread_failed_copies_lt`). Example: a thread whose first failed
  copy is of 39 entries, with 10 inserts after it, clones fewer than 2 * 39 + 2 * 10 = 98
  entries in all its failed copies together;
- so all failed copies together are at most the number of threads that ran one, times twice
  the largest the map can get plus twice the inserts (`failed_copies_le`). Example: 4 threads,
  a map that held 40 entries at the start and 10 inserts: at most 4 * (2 * 50 + 2 * 10) = 480
  entries cloned by failed copies, until a resize succeeds or the map is cleared;
- when a single thread makes all the failed copies, they add up to less than twice the first
  one plus twice the inserts (`one_thread_failed_copies_lt`).

Without the threshold none of this holds: a map going up and down between 39 and 40 entries
cloned up to 39 entries on every remove, so the total grew with the number of removes, not
with the inserts or the threads.

## The model

A state is the count, the threshold (folded, in the code, into the table's word `shrink_at`)
and, for each thread, whether it has
asked for a shrink that has not run yet. The events are the steps other threads can put in
between: an insert, a remove by a thread (which may ask), a shrink's copy that fails, a shrink
that does nothing because another resize holds the `resizing` flag, and a failed copy of a
resize no remove asked for (an insert's grow whose table another grow had already replaced,
so it asks for a smaller table than the current one). That last kind writes the threshold like
any failed shrink, but its copy is not counted by the theorems: no remove asked for it, so no
threshold could hold it back. The model has no successful resize and no clear: the theorems
are about the runs between two of them.

The model has more runs than the code, never fewer: it lets a remove ask whenever the map is
"underfull" (a free choice, `underfull`) and the threshold allows it, and it lets the steps of
different threads come in any order. A bound that holds for all of its runs holds for the
code's.
-/

namespace Kovan.HopscotchShrinkThreads

open Kovan.HopscotchShrink (ShrinkBelow thresholdAfterFailure)

/-! ## The shared map and its events -/

/-- What the threads share: the number of entries (`count`), the threshold (folded, in the
code, into the table's word `shrink_at`) and, for each thread (numbered `0, 1, 2, ...`), whether it asked for a shrink that has not run
yet: a thread between the end of its `unlink_held` and its `try_resize`.
Example: `⟨3, .unset, fun t => t == 1⟩` is a map of 3 entries with no threshold, where thread 1
has asked for a shrink. -/
structure Shared where
  count : Nat
  shrinkBelow : ShrinkBelow
  asked : Nat → Bool

/-- The steps the model interleaves. -/
inductive Event where
  /-- Some thread links a new entry: the count goes up by one (`count_in`). -/
  | insert
  /-- Thread `thread` unlinks an entry (`unlink_held`): the count goes down by one, and the
  thread asks for a shrink when the map is underfull (`underfull`, chosen freely) and the
  threshold allows the count it left. A thread that already asked is busy with its shrink and
  cannot remove; for it, and on an empty map, the step changes nothing. -/
  | remove (thread : Nat) (underfull : Bool)
  /-- The shrink that thread `thread` asked for copies the map and the copy does not fit
  (`try_resize`'s `None` arm): the threshold becomes `max (count / 2) 1`. A copy of an empty
  map always fits, so it never fails. -/
  | copyFails (thread : Nat)
  /-- The shrink that thread `thread` asked for does nothing, because another resize or a clear
  holds the `resizing` flag (`try_resize` returns at its compare-and-exchange). -/
  | copySkipped (thread : Nat)
  /-- A resize no remove asked for copies the map and the copy does not fit: an insert's
  `try_resize(capacity * 2)` whose table another grow already replaced by a larger one, so the
  size it asks for is smaller than the current table's. The threshold becomes
  `max (count / 2) 1` as for any failed shrink. Its copy is not one of the `failures` the
  theorems count: no remove asked for it, so no threshold could have held it back. -/
  | resizeFails

/-- A failed copy: the thread whose shrink it was, and how many entries the map held when it
was copied (an upper bound on the entries the copy cloned).
Example: `⟨1, 39⟩` is a failed copy of thread 1 at 39 entries. -/
structure Failed where
  thread : Nat
  count : Nat
  deriving DecidableEq, Repr

/-- What one event did: the state after it, and the failed copy it made, if it made one. -/
structure Result where
  next : Shared
  failed : Option Failed

/-- The state with thread `θ`'s "asked" mark set to `b`, every other thread's left alone. -/
def setAsked (s : Shared) (θ : Nat) (b : Bool) : Shared :=
  { s with asked := fun t => if t = θ then b else s.asked t }

/-- An insert: one entry more.
Example: 3 entries become 4. -/
def insertStep (s : Shared) : Result :=
  ⟨{ s with count := s.count + 1 }, none⟩

/-- A remove by thread `θ`. When the thread is free and the map has an entry, the count goes
down by one; then, when the map is underfull and the threshold allows the new count, the thread
is marked as having asked.
Example: with threshold `below 19`, a remove from 19 entries (leaving 18) asks; from 20 it does
not. -/
def removeStep (s : Shared) (θ : Nat) (underfull : Bool) : Result :=
  if s.asked θ = false ∧ 0 < s.count then
    if underfull = true ∧ s.shrinkBelow.Allows (s.count - 1) then
      ⟨setAsked { s with count := s.count - 1 } θ true, none⟩
    else ⟨{ s with count := s.count - 1 }, none⟩
  else ⟨s, none⟩

/-- Thread `θ`'s shrink copies the map and fails. It needs the thread to have asked and the map
to hold an entry; then the threshold becomes `max (count / 2) 1`, the thread is free again, and
the failed copy is recorded.
Example: a failed copy at 39 entries writes the threshold 19. -/
def copyFailsStep (s : Shared) (θ : Nat) : Result :=
  if s.asked θ = true ∧ 0 < s.count then
    ⟨setAsked { s with shrinkBelow := .below (thresholdAfterFailure s.count) } θ false,
      some ⟨θ, s.count⟩⟩
  else ⟨s, none⟩

/-- Thread `θ`'s shrink does nothing: the thread is free again, nothing else changes. -/
def copySkippedStep (s : Shared) (θ : Nat) : Result :=
  ⟨setAsked s θ false, none⟩

/-- A failed resize no remove asked for: the threshold is written from the count (when the map
holds an entry), and no failed copy of a remove's shrink is recorded. -/
def resizeFailsStep (s : Shared) : Result :=
  if 0 < s.count then ⟨{ s with shrinkBelow := .below (thresholdAfterFailure s.count) }, none⟩
  else ⟨s, none⟩

/-- One event on the shared state. -/
def step (s : Shared) : Event → Result
  | .insert => insertStep s
  | .remove θ underfull => removeStep s θ underfull
  | .copyFails θ => copyFailsStep s θ
  | .copySkipped θ => copySkippedStep s θ
  | .resizeFails => resizeFailsStep s

/-- The failed copy of one step if it was thread `θ`'s, as its count.
Example: a step that made the failed copy `⟨1, 39⟩` gives `some 39` for thread 1 and `none`
for thread 2. -/
def ownFailure (θ : Nat) (r : Result) : Option Nat :=
  match r.failed with
  | some f => if f.thread = θ then some f.count else none
  | none => none

/-- The counts of thread `θ`'s failed copies in a run, in order. -/
def failuresOf (θ : Nat) (s : Shared) : List Event → List Nat
  | [] => []
  | e :: run => (ownFailure θ (step s e)).toList ++ failuresOf θ (step s e).next run

/-- Every failed copy of a run, of every thread, in order. -/
def failures (s : Shared) : List Event → List Failed
  | [] => []
  | e :: run => (step s e).failed.toList ++ failures (step s e).next run

/-- The entries all the failed copies of a run cloned at most, together. -/
def totalCopies (s : Shared) (run : List Event) : Nat :=
  ((failures s run).map Failed.count).sum

/-- The number of inserts in a run.
Example: `[.insert, .remove 1 true, .insert]` has 2. -/
def insertsIn : List Event → Nat
  | [] => 0
  | .insert :: run => insertsIn run + 1
  | .remove _ _ :: run => insertsIn run
  | .copyFails _ :: run => insertsIn run
  | .copySkipped _ :: run => insertsIn run
  | .resizeFails :: run => insertsIn run

/-- The number of inserts in a run after thread `θ`'s first failed copy (all the inserts of the
run when the thread makes none, which no theorem uses).
Example: in `[.insert, <θ's first failed copy>, .insert, .insert]` it is 2. -/
def insertsAfterFirst (θ : Nat) (s : Shared) : List Event → Nat
  | [] => 0
  | e :: run =>
    match ownFailure θ (step s e) with
    | some _ => insertsIn run
    | none => insertsAfterFirst θ (step s e).next run

/-- There are never more inserts after the first failed copy than in the whole run. -/
theorem insertsAfterFirst_le (θ : Nat) :
    ∀ (run : List Event) (s : Shared), insertsAfterFirst θ s run ≤ insertsIn run := by
  intro run
  induction run with
  | nil => intro s; exact Nat.le_refl _
  | cons e run ih =>
    intro s
    -- The rest of the run has at most the inserts of the whole run.
    have hins : insertsIn run ≤ insertsIn (e :: run) := by
      cases e <;> simp only [insertsIn] <;> omega
    simp only [insertsAfterFirst]
    split
    · exact hins
    · exact Nat.le_trans (ih _) hins

/-! ## The example: two threads fail at the same count -/

/-- Four entries, no threshold, nobody has asked. -/
def fourEntries : Shared := ⟨4, .unset, fun _ => false⟩

/-- Threads 1 and 2 each remove an entry and ask (counts 3 and 2), then both shrinks run and
fail. Thread 2 asked before thread 1's failure wrote its threshold (1), so its shrink runs
anyway, at the same count 2 as thread 1's. With one thread, the second failure would have had
to be at fewer than half the first; here it is at the same count. Lean checks this by running
the four steps. -/
theorem two_threads_fail_at_the_same_count :
    failures fourEntries [.remove 1 true, .remove 2 true, .copyFails 1, .copyFails 2] =
      [⟨1, 2⟩, ⟨2, 2⟩] := by
  -- Computing the run step by step gives exactly these two failed copies.
  rfl

/-! ## Facts about single steps -/

/-- Reading a thread's mark after `setAsked`: the thread set gets `b`, any other keeps its
mark. -/
theorem setAsked_asked (s : Shared) (θ t : Nat) (b : Bool) :
    (setAsked s θ b).asked t = if t = θ then b else s.asked t := rfl

/-- A remove never makes a failed copy: in every branch of `removeStep`, `failed` is `none`. -/
theorem removeStep_failed (s : Shared) (θ : Nat) (u : Bool) : (removeStep s θ u).failed = none := by
  unfold removeStep
  -- Each of the three branches builds its result with `none`.
  split
  · split <;> rfl
  · rfl

/-- After a remove the count went down by one, or stayed the same (a busy thread, an empty
map). Either way it is not higher. -/
theorem removeStep_count_le (s : Shared) (θ : Nat) (u : Bool) :
    (removeStep s θ u).next.count ≤ s.count := by
  unfold removeStep
  split
  · -- The remove happened: the count is `s.count - 1` in both inner branches.
    split
    · exact Nat.sub_le _ _
    · exact Nat.sub_le _ _
  · -- Nothing happened.
    exact Nat.le_refl _

/-- A remove does not touch the threshold. -/
theorem removeStep_shrinkBelow (s : Shared) (θ : Nat) (u : Bool) :
    (removeStep s θ u).next.shrinkBelow = s.shrinkBelow := by
  unfold removeStep
  -- No branch writes `shrinkBelow` (`setAsked` only touches the marks).
  split
  · split <;> rfl
  · rfl

/-- A skipped shrink makes no failed copy, keeps the count and keeps the threshold. -/
theorem copySkippedStep_facts (s : Shared) (θ : Nat) :
    (copySkippedStep s θ).failed = none ∧ (copySkippedStep s θ).next.count = s.count ∧
      (copySkippedStep s θ).next.shrinkBelow = s.shrinkBelow := ⟨rfl, rfl, rfl⟩

/-- A failed resize no remove asked for makes no recorded failed copy, keeps the count and the
marks, and leaves the threshold either as it was (empty map) or written from the count. -/
theorem resizeFailsStep_facts (s : Shared) :
    (resizeFailsStep s).failed = none ∧ (resizeFailsStep s).next.count = s.count ∧
      (resizeFailsStep s).next.asked = s.asked ∧
      ((resizeFailsStep s).next.shrinkBelow = s.shrinkBelow ∨
        (resizeFailsStep s).next.shrinkBelow = .below (thresholdAfterFailure s.count)) := by
  unfold resizeFailsStep
  -- Both branches build their result with `none`, the same count and the same marks.
  split
  · exact ⟨rfl, rfl, rfl, Or.inr rfl⟩
  · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩

/-- A failed copy keeps the count: copying reads the entries, it removes none. -/
theorem copyFailsStep_count (s : Shared) (θ : Nat) :
    (copyFailsStep s θ).next.count = s.count := by
  unfold copyFailsStep
  split <;> rfl

/-- What a copy step made: either nothing (the thread had not asked, or the map was empty) and
the state is unchanged, or a failed copy of thread `θ` at the current count, with the
threshold set from that count and the thread free again. -/
theorem copyFailsStep_cases (s : Shared) (θ : Nat) :
    ((copyFailsStep s θ).failed = none ∧ (copyFailsStep s θ).next = s) ∨
    (s.asked θ = true ∧ 0 < s.count ∧
      (copyFailsStep s θ).failed = some ⟨θ, s.count⟩ ∧
      (copyFailsStep s θ).next =
        setAsked { s with shrinkBelow := .below (thresholdAfterFailure s.count) } θ false) := by
  unfold copyFailsStep
  split
  · -- The thread had asked and the map has an entry: the second case.
    rename_i h
    exact Or.inr ⟨h.1, h.2, rfl, rfl⟩
  · -- Otherwise nothing happened: the first case.
    exact Or.inl ⟨rfl, rfl⟩

/-- The arithmetic of a threshold written at a count no larger than a budget `B` of at least 1:
twice the threshold is at most `B + 1`.
Example: a count of 39 with a budget of 39 writes 19, and 2 * 19 = 38 is at most 40.
Why: if the count is 2 or more, the threshold is half the count, rounded down, so twice it is
at most the count; if the count is 0 or 1, the threshold is 1 and `2 ≤ B + 1`. -/
theorem twice_threshold_le (n B : Nat) (hn : n ≤ B) (hB : 1 ≤ B) :
    2 * thresholdAfterFailure n ≤ B + 1 := by
  unfold thresholdAfterFailure
  -- Linear arithmetic with `max` and halving (`omega`) on the two cases above.
  omega

/-! ## The bound for one thread

Fix a thread `θ`. Once it has made a failed copy, five numbers describe where it stands:

- `S`, the total of its failed copies so far;
- `L`, the count of its last failed copy (at least 1);
- `ins`, the inserts since that last failed copy;
- `K`, its allowance: twice its first failed copy, plus twice every insert since then.

`Budget` says these numbers keep the thread's future failed copies small. The proof shows that
every event keeps `Budget` true, and that at the end `Budget` gives `S < K`. -/

/-- The thread's budget, in five facts:
1. its last failed copy had at least one entry;
2. its total so far, its last copy and twice the inserts since fit in its allowance;
3. the map holds at most its last copy's count plus the inserts since;
4. the threshold is `below t` with `2 * t` at most that same number plus 1;
5. if the thread has asked for a shrink, twice the count plus 1 is at most its last copy's
   count plus twice the inserts since (what its next failed copy can cost).
Example: right after a failed copy at 39 entries that is the thread's first, `S = 39`,
`L = 39`, `ins = 0`, `K = 78`, and the threshold is 19: all five facts hold. -/
def Budget (θ : Nat) (s : Shared) (S L ins K : Nat) : Prop :=
  1 ≤ L ∧ S + L + 2 * ins ≤ K ∧ s.count ≤ L + ins ∧
    (∃ t, s.shrinkBelow = .below t ∧ 2 * t ≤ L + ins + 1) ∧
    (s.asked θ = true → 2 * s.count + 1 ≤ L + 2 * ins)

/-- An insert keeps the budget, with one more insert counted and an allowance 2 larger.
Why: the count and the inserts both go up by one, so facts 3 to 5 keep their slack, and fact 2
gains 2 on both sides. -/
theorem budget_insert (θ : Nat) (s : Shared) (S L ins K : Nat) (h : Budget θ s S L ins K) :
    Budget θ (insertStep s).next S L (ins + 1) (K + 2) := by
  obtain ⟨hL, hK, hc, ⟨t, ht, h2t⟩, hask⟩ := h
  refine ⟨hL, ?_, ?_, ⟨t, ht, ?_⟩, ?_⟩
  · -- Fact 2: both sides grow by 2.
    omega
  · -- Fact 3: the count and the inserts both grow by 1.
    show s.count + 1 ≤ L + (ins + 1)
    omega
  · -- Fact 4: the threshold is unchanged and its bound only grew.
    omega
  · -- Fact 5: the marks are unchanged; twice the count grows by 2, and so does the right side.
    intro ha
    have := hask ha
    show 2 * (s.count + 1) + 1 ≤ L + 2 * (ins + 1)
    omega

/-- A remove by any thread keeps the budget, with the same numbers.
Why: the count does not grow, the threshold does not change, and if the remove is `θ`'s own and
it asks, the threshold allowed the count it left: that count is below `t`, and `2 * t` is at
most `L + ins + 1`, which gives fact 5. -/
theorem budget_remove (θ θ' : Nat) (u : Bool) (s : Shared) (S L ins K : Nat)
    (h : Budget θ s S L ins K) : Budget θ (removeStep s θ' u).next S L ins K := by
  obtain ⟨hL, hK, hc, ⟨t, ht, h2t⟩, hask⟩ := h
  refine ⟨hL, hK, ?_, ⟨t, ?_, h2t⟩, ?_⟩
  · -- Fact 3: the count did not grow (`removeStep_count_le`).
    exact Nat.le_trans (removeStep_count_le s θ' u) hc
  · -- Fact 4: the threshold did not change (`removeStep_shrinkBelow`).
    rw [removeStep_shrinkBelow]; exact ht
  · -- Fact 5: look at what the remove did.
    intro ha
    unfold removeStep at ha ⊢
    by_cases hgo : s.asked θ' = false ∧ 0 < s.count
    · rw [ite_eq_left hgo] at ha ⊢
      by_cases hask' : u = true ∧ s.shrinkBelow.Allows (s.count - 1)
      · rw [ite_eq_left hask'] at ha ⊢
        -- The remove asked. The thread whose mark we read is `θ`.
        rw [setAsked_asked] at ha
        by_cases hθ : θ = θ'
        · -- It is `θ`'s own ask: the count it left is below `t`.
          have hallow := hask'.2
          rw [ht] at hallow
          simp only [ShrinkBelow.Allows] at hallow
          show 2 * (s.count - 1) + 1 ≤ L + 2 * ins
          -- `s.count - 1 < t` and `2 * t ≤ L + ins + 1` (linear arithmetic, `omega`).
          omega
        · -- Another thread asked: `θ`'s mark is the old one, so fact 5 held before, and the
          -- count only went down.
          rw [ite_eq_right hθ] at ha
          have := hask ha
          show 2 * (s.count - 1) + 1 ≤ L + 2 * ins
          omega
      · rw [ite_eq_right hask'] at ha ⊢
        -- The remove did not ask: the marks are the old ones and the count went down.
        have := hask ha
        show 2 * (s.count - 1) + 1 ≤ L + 2 * ins
        omega
    · rw [ite_eq_right hgo] at ha ⊢
      -- Nothing happened: fact 5 is the old one.
      exact hask ha

/-- A skipped shrink keeps the budget, with the same numbers.
Why: only a mark changes, to "not asked", which can only make fact 5 easier. -/
theorem budget_skipped (θ θ' : Nat) (s : Shared) (S L ins K : Nat)
    (h : Budget θ s S L ins K) : Budget θ (copySkippedStep s θ').next S L ins K := by
  obtain ⟨hL, hK, hc, ht, hask⟩ := h
  refine ⟨hL, hK, hc, ht, ?_⟩
  intro ha
  -- The count is the same; if `θ`'s mark is still "asked", it was "asked" before.
  show 2 * s.count + 1 ≤ L + 2 * ins
  simp only [copySkippedStep, setAsked_asked] at ha
  by_cases hθ : θ = θ'
  · -- `θ`'s own shrink was skipped: its mark is now `false`, not `true`.
    rw [ite_eq_left hθ] at ha
    exact absurd ha (by decide)
  · rw [ite_eq_right hθ] at ha
    exact hask ha

/-- Another thread's failed copy keeps `θ`'s budget, with the same numbers.
Why: the count is the same, and the new threshold is written from the current count, which is
at most `L + ins` (fact 3), so `twice_threshold_le` gives fact 4. `θ`'s mark is untouched. -/
theorem budget_other_fails (θ θ' : Nat) (hne : θ' ≠ θ) (s : Shared) (S L ins K : Nat)
    (h : Budget θ s S L ins K) : Budget θ (copyFailsStep s θ').next S L ins K := by
  rcases copyFailsStep_cases s θ' with ⟨_, hnext⟩ | ⟨_, _, _, hnext⟩
  · -- Nothing happened.
    rw [hnext]; exact h
  · obtain ⟨hL, hK, hc, _, hask⟩ := h
    rw [hnext]
    refine ⟨hL, hK, hc, ⟨thresholdAfterFailure s.count, rfl, ?_⟩, ?_⟩
    · -- Fact 4 for the new threshold (`twice_threshold_le`, the count being at most `L + ins`,
      -- and `L + ins` at least 1).
      exact twice_threshold_le s.count (L + ins) hc (by omega)
    · -- Fact 5: `θ`'s mark is the old one (`θ ≠ θ'`) and the count is the same.
      intro ha
      rw [setAsked_asked, ite_eq_right (Ne.symm hne)] at ha
      exact hask ha

/-- A failed resize no remove asked for keeps `θ`'s budget, with the same numbers, for the same
reason as another thread's failed copy: the new threshold is written from a count of at most
`L + ins`. -/
theorem budget_resize_fails (θ : Nat) (s : Shared) (S L ins K : Nat)
    (h : Budget θ s S L ins K) : Budget θ (resizeFailsStep s).next S L ins K := by
  obtain ⟨hf, hcount, hasked, hsb⟩ := resizeFailsStep_facts s
  obtain ⟨hL, hK, hc, ⟨t, ht, h2t⟩, hask⟩ := h
  refine ⟨hL, hK, by rw [hcount]; exact hc, ?_, ?_⟩
  · rcases hsb with hsb | hsb
    · -- The threshold did not change.
      exact ⟨t, by rw [hsb]; exact ht, h2t⟩
    · -- The threshold was written from the count (`twice_threshold_le`).
      exact ⟨thresholdAfterFailure s.count, hsb,
        twice_threshold_le s.count (L + ins) hc (by omega)⟩
  · -- The marks and the count are the old ones, so fact 5 is the old one.
    intro ha
    rw [hasked] at ha
    rw [hcount]
    exact hask ha

/-- `θ`'s own failed copy at `c` entries starts the budget again: total `S + c`, last copy `c`,
no inserts since, the same allowance.
Why: the thread had asked, so fact 5 says `2 * c + 1 ≤ L + 2 * ins`; with fact 2,
`S + c + c` fits in `K`. The new threshold is written from `c` itself, so facts 3 and 4 hold
with `L = c` and no inserts, and the thread is free again, so fact 5 says nothing. -/
theorem budget_own_fails (θ : Nat) (s : Shared) (S L ins K : Nat) (h : Budget θ s S L ins K)
    (hasked : s.asked θ = true) (hpos : 0 < s.count) :
    Budget θ (setAsked { s with shrinkBelow := .below (thresholdAfterFailure s.count) } θ false)
      (S + s.count) s.count 0 K := by
  obtain ⟨_, hK, _, _, hask⟩ := h
  have h5 := hask hasked
  refine ⟨hpos, ?_, ?_, ⟨thresholdAfterFailure s.count, rfl, ?_⟩, ?_⟩
  · -- Fact 2: `S + c + c ≤ S + L + 2 * ins - 1 ≤ K` (linear arithmetic with facts 2 and 5).
    omega
  · -- Fact 3: the count is `c` itself.
    show s.count ≤ s.count + 0
    omega
  · -- Fact 4: the threshold written from `c` (`twice_threshold_le` with the budget `c`).
    exact twice_threshold_le s.count (s.count + 0) (by omega) (by omega)
  · -- Fact 5: the thread is free again, so "asked" is false.
    intro ha
    rw [setAsked_asked, ite_eq_left rfl] at ha
    exact absurd ha (by decide)

/-- Once thread `θ` has made a failed copy and its budget holds, every run keeps its total
below its allowance: the total so far plus everything it copies in the rest of the run is less
than `K` plus twice the inserts of the run.
Example: right after a first failed copy at 39 (`S = 39`, `K = 78`), a run with 10 inserts
leaves the thread's total below 78 + 20 = 98. -/
theorem budget_run (θ : Nat) :
    ∀ (run : List Event) (s : Shared) (S L ins K : Nat), Budget θ s S L ins K →
      S + (failuresOf θ s run).sum < K + 2 * insertsIn run := by
  intro run
  induction run with
  | nil =>
    -- No more events: facts 1 and 2 give `S < K`.
    intro s S L ins K h
    obtain ⟨hL, hK, _⟩ := h
    simp only [failuresOf, List.sum_nil, insertsIn]
    omega
  | cons e run ih =>
    intro s S L ins K h
    cases e with
    | insert =>
      -- An insert makes no failed copy and keeps the budget with one more insert and 2 more
      -- allowance (`budget_insert`); the run after it then stays below that allowance.
      have hrest := ih _ S L (ins + 1) (K + 2) (budget_insert θ s S L ins K h)
      simp only [failuresOf, step, insertStep, ownFailure, Option.toList, List.nil_append,
        insertsIn] at hrest ⊢
      omega
    | remove θ' u =>
      -- A remove makes no failed copy and keeps the budget (`budget_remove`).
      have hrest := ih _ S L ins K (budget_remove θ θ' u s S L ins K h)
      simp only [failuresOf, step, ownFailure, removeStep_failed, Option.toList,
        List.nil_append, insertsIn] at hrest ⊢
      exact hrest
    | copySkipped θ' =>
      -- A skipped shrink makes no failed copy and keeps the budget (`budget_skipped`).
      have hrest := ih _ S L ins K (budget_skipped θ θ' s S L ins K h)
      simp only [failuresOf, step, ownFailure, copySkippedStep, Option.toList,
        List.nil_append, insertsIn] at hrest ⊢
      exact hrest
    | resizeFails =>
      -- A failed resize no remove asked for records no failed copy and keeps the budget
      -- (`budget_resize_fails`).
      have hrest := ih _ S L ins K (budget_resize_fails θ s S L ins K h)
      simp only [failuresOf, step, ownFailure, (resizeFailsStep_facts s).1, Option.toList,
        List.nil_append, insertsIn] at hrest ⊢
      exact hrest
    | copyFails θ' =>
      simp only [failuresOf, step, insertsIn]
      by_cases hθ : θ' = θ
      · -- The copy is `θ`'s own.
        subst hθ
        rcases copyFailsStep_cases s θ' with ⟨hf, hnext⟩ | ⟨hasked, hpos, hf, hnext⟩
        · -- It did nothing: no failed copy, same state, same budget.
          have hrest := ih s S L ins K h
          simp only [ownFailure, hf, hnext, Option.toList, List.nil_append]
          exact hrest
        · -- It failed at `c = s.count`: the thread's total grows by `c`, and the budget
          -- starts again from `c` (`budget_own_fails`); the rest of the run stays below the
          -- same allowance.
          have hrest := ih _ (S + s.count) s.count 0 K
            (hnext ▸ budget_own_fails θ' s S L ins K h hasked hpos)
          simp only [ownFailure, hf, ↓reduceIte, Option.toList, List.singleton_append,
            List.sum_cons, hnext] at hrest ⊢
          omega
      · -- Another thread's copy: no failed copy of `θ`, and the budget holds
        -- (`budget_other_fails`).
        have hrest := ih _ S L ins K (budget_other_fails θ θ' hθ s S L ins K h)
        have hown : ownFailure θ (copyFailsStep s θ') = none := by
          rcases copyFailsStep_cases s θ' with ⟨hf, _⟩ | ⟨_, _, hf, _⟩
          · simp only [ownFailure, hf]
          · simp only [ownFailure, hf, ite_eq_right hθ]
        simp only [hown, Option.toList, List.nil_append]
        exact hrest

/-- The bound for each thread, tight form: if thread `θ`'s failed copies in a run are
`c :: rest`, their total is less than twice the first one plus twice the inserts that came
after that first one.
Example: a thread whose first failed copy is at 39, with 10 inserts after it, clones fewer
than 98 entries in all its failed copies; inserts before its first failed copy do not count.
Why: before its first failed copy nothing is counted; at it, the budget starts with total `c`,
last copy `c`, no inserts and allowance `2 * c` (all five facts hold), and `budget_run` keeps
the rest below `2 * c` plus twice the inserts after it. -/
theorem thread_failed_copies_lt_after (θ : Nat) :
    ∀ (run : List Event) (s : Shared) (c : Nat) (rest : List Nat),
      failuresOf θ s run = c :: rest →
        (c :: rest).sum < 2 * c + 2 * insertsAfterFirst θ s run := by
  intro run
  induction run with
  | nil =>
    -- An empty run has no failed copy, so this case cannot happen.
    intro s c rest h
    simp [failuresOf] at h
  | cons e run ih =>
    intro s c rest h
    -- Does this first event make `θ`'s first failed copy?
    cases hown : ownFailure θ (step s e) with
    | none =>
      -- No: the failed copies, and the inserts after the first of them, are those of the rest
      -- of the run.
      simp only [failuresOf, hown, Option.toList, List.nil_append] at h
      simp only [insertsAfterFirst, hown]
      exact ih _ c rest h
    | some c' =>
      -- Yes, at `c'`: it is the first in the list, so `c' = c`, and the inserts after it are
      -- the inserts of the rest of the run.
      simp only [failuresOf, hown, Option.toList, List.singleton_append, List.cons.injEq] at h
      obtain ⟨hc, hrest⟩ := h
      subst hc
      simp only [insertsAfterFirst, hown]
      -- Only a copy step makes a failed copy, and it must be `θ`'s own, at the current count.
      cases e with
      | insert => simp [ownFailure, step, insertStep] at hown
      | remove _ _ => simp [ownFailure, step, removeStep_failed] at hown
      | copySkipped _ => simp [ownFailure, step, copySkippedStep] at hown
      | resizeFails => simp [ownFailure, step, (resizeFailsStep_facts s).1] at hown
      | copyFails θ' =>
        rcases copyFailsStep_cases s θ' with ⟨hf, _⟩ | ⟨hasked, hpos, hf, hnext⟩
        · simp [ownFailure, step, hf] at hown
        · -- The failed copy is `θ'`'s at `s.count`; it is `θ`'s, so `θ' = θ` and `c = s.count`.
          simp only [ownFailure, step, hf] at hown
          by_cases hθ : θ' = θ
          · rw [ite_eq_left hθ] at hown
            simp only [Option.some.injEq] at hown
            subst hθ
            subst hown
            -- Start the budget at this failed copy: total `c`, last copy `c`, no inserts since,
            -- allowance `2 * c`. Its five facts hold (the threshold was just written from `c`,
            -- and the thread is free again), so `budget_run` bounds the rest of the run.
            have hb : Budget θ' (step s (.copyFails θ')).next s.count s.count 0 (2 * s.count) := by
              simp only [step, hnext]
              refine ⟨hpos, by omega, by show s.count ≤ s.count + 0; omega,
                ⟨thresholdAfterFailure s.count, rfl,
                  twice_threshold_le s.count (s.count + 0) (by omega) (by omega)⟩, ?_⟩
              intro ha
              rw [setAsked_asked, ite_eq_left rfl] at ha
              exact absurd ha (by decide)
            have := budget_run θ' run _ s.count s.count 0 (2 * s.count) hb
            rw [hrest] at this
            simp only [List.sum_cons]
            omega
          · rw [ite_eq_right hθ] at hown
            exact absurd hown (by simp)

/-- The bound for each thread: if thread `θ`'s failed copies in a run are `c :: rest`, their
total is less than twice the first one plus twice the inserts of the run.
Example: a thread whose first failed copy is at 39, in a run with 10 inserts, clones fewer than
98 entries in all its failed copies.
Why: the tight form counts only the inserts after the first failed copy, which are at most all
of them (`insertsAfterFirst_le`). -/
theorem thread_failed_copies_lt (θ : Nat) (run : List Event) (s : Shared) (c : Nat)
    (rest : List Nat) (h : failuresOf θ s run = c :: rest) :
    (c :: rest).sum < 2 * c + 2 * insertsIn run := by
  have hlt := thread_failed_copies_lt_after θ run s c rest h
  have hle := insertsAfterFirst_le θ run s
  omega

/-! ## The bound for all threads together -/

/-- Every failed copy of thread `θ` is at most the count at the start plus the inserts of the
run: the count only grows by inserts.
Example: a map of 40 entries with 10 inserts never makes a failed copy of more than 50. -/
theorem failuresOf_le (θ : Nat) :
    ∀ (run : List Event) (s : Shared), ∀ c ∈ failuresOf θ s run, c ≤ s.count + insertsIn run := by
  intro run
  induction run with
  | nil =>
    -- No failed copies in an empty run.
    intro s c hc
    simp [failuresOf] at hc
  | cons e run ih =>
    intro s c hc
    simp only [failuresOf, List.mem_append] at hc
    -- After one event the count is at most one more (an insert) than before.
    have hstep : (step s e).next.count ≤ s.count + (insertsIn (e :: run) - insertsIn run) := by
      cases e with
      | insert => simp only [step, insertStep, insertsIn]; omega
      | remove θ' u =>
        simp only [step, insertsIn]; have := removeStep_count_le s θ' u; omega
      | copyFails θ' => simp only [step, insertsIn, copyFailsStep_count]; omega
      | copySkipped θ' => simp only [step, insertsIn, (copySkippedStep_facts s θ').2.1]; omega
      | resizeFails => simp only [step, insertsIn, (resizeFailsStep_facts s).2.1]; omega
    have hins : insertsIn run ≤ insertsIn (e :: run) := by
      cases e <;> simp only [insertsIn] <;> omega
    rcases hc with hc | hc
    · -- `c` is this event's failed copy: a copy step, at the current count.
      cases e with
      | insert => simp [ownFailure, step, insertStep] at hc
      | remove _ _ => simp [ownFailure, step, removeStep_failed] at hc
      | copySkipped _ => simp [ownFailure, step, copySkippedStep] at hc
      | resizeFails => simp [ownFailure, step, (resizeFailsStep_facts s).1] at hc
      | copyFails θ' =>
        rcases copyFailsStep_cases s θ' with ⟨hf, _⟩ | ⟨_, _, hf, _⟩
        · simp [ownFailure, step, hf] at hc
        · simp only [ownFailure, step, hf] at hc
          split at hc
          · simp only [Option.toList, List.mem_singleton] at hc
            omega
          · simp at hc
    · -- `c` comes later: at most the count after this event plus the later inserts.
      have := ih _ c hc
      omega

/-- The sum over a list of threads of `f θ + g θ` is the sum of `f` plus the sum of `g`. -/
theorem sum_map_add (ths : List Nat) (f g : Nat → Nat) :
    (ths.map fun θ => f θ + g θ).sum = (ths.map f).sum + (ths.map g).sum := by
  induction ths with
  | nil => rfl
  | cons θ ths ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

/-- A sum over a list of threads of values each at most `B` is at most the length times `B`. -/
theorem sum_map_le (ths : List Nat) (f : Nat → Nat) (B : Nat) (h : ∀ θ ∈ ths, f θ ≤ B) :
    (ths.map f).sum ≤ ths.length * B := by
  induction ths with
  | nil => simp
  | cons θ ths ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h θ (List.mem_cons_self ..)
    have h2 := ih (fun θ' hm => h θ' (List.mem_cons_of_mem _ hm))
    rw [Nat.succ_mul]
    omega

/-- A failed copy of a step, of a thread in the list `ths`, is counted at least once when the
step's own failed copies are summed over `ths`. -/
theorem own_sum_ge (r : Result) (f : Failed) (hf : r.failed = some f) :
    ∀ (ths : List Nat), f.thread ∈ ths →
      f.count ≤ (ths.map fun θ => (ownFailure θ r).toList.sum).sum := by
  intro ths
  induction ths with
  | nil => intro h; simp at h
  | cons θ ths ih =>
    intro hmem
    simp only [List.map_cons, List.sum_cons]
    by_cases hθ : f.thread = θ
    · -- This thread is the one: its own failed copy is `f.count`.
      simp only [ownFailure, hf, ite_eq_left hθ, Option.toList, List.sum_cons, List.sum_nil]
      omega
    · -- Another thread: the copy is counted further down the list.
      have hin : f.thread ∈ ths := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h hθ
        · exact h
      have := ih hin
      omega

/-- All the failed copies of a run are at most the sum, over a list of threads that covers
every failed copy, of each thread's failed copies. -/
theorem total_le_sum_threads :
    ∀ (run : List Event) (s : Shared) (ths : List Nat),
      (∀ f ∈ failures s run, f.thread ∈ ths) →
      totalCopies s run ≤ (ths.map fun θ => (failuresOf θ s run).sum).sum := by
  intro run
  induction run with
  | nil => intro s ths _; simp [totalCopies, failures]
  | cons e run ih =>
    intro s ths h
    -- Split each side into this event's part and the rest of the run's part.
    have hrest := ih (step s e).next ths
      (fun f hf => h f (by simp only [failures, List.mem_append]; exact Or.inr hf))
    have hsplit : (ths.map fun θ => (failuresOf θ s (e :: run)).sum).sum =
        (ths.map fun θ => (ownFailure θ (step s e)).toList.sum).sum +
          (ths.map fun θ => (failuresOf θ (step s e).next run).sum).sum := by
      simp only [failuresOf, List.sum_append]
      exact sum_map_add ths _ _
    rw [hsplit]
    unfold totalCopies at hrest ⊢
    simp only [failures, List.map_append, List.sum_append]
    -- This event's failed copy, if any, belongs to a thread of `ths` and is counted there
    -- (`own_sum_ge`).
    cases hf : (step s e).failed with
    | none => simp only [Option.toList_none, List.map_nil, List.sum_nil]; omega
    | some f =>
      have hmem : f.thread ∈ ths := h f (by simp [failures, hf])
      have := own_sum_ge (step s e) f hf ths hmem
      simp only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      omega

/-- The bound for all threads together: between two erasures, the entries cloned by all failed
copies are at most the number of threads that made one, times twice the largest the map can
get (the count at the start plus the inserts) plus twice the inserts.
Example: 4 threads, 40 entries at the start, 10 inserts: at most 4 * (2 * 50 + 2 * 10) = 480.
Why: each thread's failed copies are below twice its first plus twice the inserts
(`thread_failed_copies_lt`), its first is at most the count at the start plus the inserts
(`failuresOf_le`), and adding up the threads counts every failed copy (`total_le_sum_threads`). -/
theorem failed_copies_le (s : Shared) (run : List Event) (ths : List Nat)
    (h : ∀ f ∈ failures s run, f.thread ∈ ths) :
    totalCopies s run ≤
      ths.length * (2 * (s.count + insertsIn run) + 2 * insertsIn run) := by
  refine Nat.le_trans (total_le_sum_threads run s ths h) (sum_map_le ths _ _ ?_)
  intro θ _
  -- One thread's total: zero if it made no failed copy, else below its bound.
  cases hθ : failuresOf θ s run with
  | nil => simp
  | cons c rest =>
    have hlt := thread_failed_copies_lt θ run s c rest hθ
    have hc := failuresOf_le θ run s c (by rw [hθ]; exact List.mem_cons_self ..)
    omega

/-- With a single thread making failed copies, they add up to less than twice the first one
plus twice the inserts of the run.
Example: one remover whose first failed copy is at 39, in a run with 10 inserts by other
threads, clones fewer than 98 entries in all. -/
theorem one_thread_failed_copies_lt (s : Shared) (run : List Event) (θ c : Nat)
    (rest : List Nat) (h : ∀ f ∈ failures s run, f.thread = θ)
    (hθ : failuresOf θ s run = c :: rest) :
    totalCopies s run < 2 * c + 2 * insertsIn run := by
  -- All failed copies are `θ`'s, so the total is at most `θ`'s total (`total_le_sum_threads`
  -- with the list `[θ]`), which is below the bound (`thread_failed_copies_lt`).
  have hle := total_le_sum_threads run s [θ] (fun f hf => by simp [h f hf])
  have hlt := thread_failed_copies_lt θ run s c rest hθ
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hθ] at hle
  simp only [List.sum_cons] at hlt
  omega

end Kovan.HopscotchShrinkThreads
