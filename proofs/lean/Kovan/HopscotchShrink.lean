/-!
# The hopscotch map's shrink threshold

This file checks one rule of `HopscotchMap` (`kovan-map/src/hopscotch.rs` and
`kovan-map/src/hopscotch/resize.rs`): after a shrink that could not fit, the map does not try
again until half of the entries it had then are gone.

## The story in plain words

A `HopscotchMap` keeps its entries in a table of buckets. When a remove leaves the table less
than a quarter full, the map tries to halve the table: it copies every entry into a new table
of half the size. Sometimes the entries do not fit there (too many of them land near the same
bucket), and the copy is thrown away. That copy was work for nothing: one clone of a key and a
value for every entry it copied.

Before the fix, the very next remove asked for the same shrink and failed the same way. A map
holding 39 entries that saw one insert and one remove at a time paid for a useless copy of up
to 39 entries on every remove. Now a failed shrink at 39 entries writes down 19 (half of 39,
rounded down) as its threshold, and no remove asks for a shrink again until fewer than 19
entries are left. A resize that succeeds, or a `clear`, erases what was written down. (The code
keeps the threshold folded into one word of the table; the last section proves the fold exact.)

This file proves, for every possible sequence of operations:

1. every successful resize and every clear erase the threshold;
2. after a failed shrink at `c` entries, and until the next erasure, no shrink is asked for
   while at least `max (c / 2) 1` entries remain, and the first remove that leaves fewer while
   the map is underfull does ask;
3. between two erasures, each failed shrink happens at fewer than half the entries of the one
   before, so all their copies together are fewer than twice the entries of the first one.

## What the model leaves out

The model is one thread doing one operation at a time; the TLA+ model in
`proofs/tla/hopscotch` checks the concurrent steps. It does not place entries in buckets, so
whether a shrink fits is a free choice made with each remove, with one exception taken from
the code: a map with no entries always fits, because there is no entry that could fail to
find a place. The theorems therefore hold whatever the keys and their hashes are.
-/

namespace Kovan.HopscotchShrink

/-! ## The map -/

/-- `MIN_CAPACITY` in `kovan-map/src/hopscotch.rs`: the map never shrinks below 64 buckets.
Example: a table of 64 buckets is never underfull, however empty it is. -/
def minCapacity : Nat := 64

/-- Underfull: fewer than a quarter of the buckets hold an entry, in a table bigger than the
smallest one. The code tests it as `count < shrink_at(capacity)` (`lt_shrinkAt_iff` below).
Example: 39 entries in 256 buckets are underfull (4 * 39 = 156 is less than 256); 64 entries
are not (4 * 64 = 256 is not less than 256). -/
def Underfull (count capacity : Nat) : Prop :=
  4 * count < capacity ∧ minCapacity < capacity

/-- Lean can compute whether a table is underfull: both halves are comparisons of numbers. -/
instance (count capacity : Nat) : Decidable (Underfull count capacity) := by
  unfold Underfull
  infer_instance

/-- The threshold a failed shrink wrote down, or none. The code folds it into the table's word
`shrink_at` (`word` below); here "none" is a case of its own, `unset`, so no theorem needs a
number standing for "no threshold". -/
inductive ShrinkBelow where
  /-- No failed shrink since the last erasure: the table's word is its quarter. -/
  | unset
  /-- A failed shrink wrote down `n`: a remove asks for a shrink only when it leaves fewer than
  `n` entries. -/
  | below (n : Nat)
  deriving DecidableEq, Repr

/-- Whether the threshold lets a remove that leaves `count` entries ask for a shrink: the
threshold half of the test the code folds into one compare at the end of `unlink_held`.
Examples: `unset` lets every count through; `below 19` lets 18 through but not 19. -/
def ShrinkBelow.Allows : ShrinkBelow → Nat → Prop
  | .unset, _ => True
  | .below n, count => count < n

/-- Lean can compute `Allows`: it is either `True` or one comparison. -/
instance (t : ShrinkBelow) (count : Nat) : Decidable (t.Allows count) := by
  cases t <;> unfold ShrinkBelow.Allows <;> infer_instance

/-- What the model keeps of a `HopscotchMap`: the number of entries (the field `count`), the
number of buckets of the current table (`capacity`) and the threshold (folded, in the code,
into the current table's word `shrink_at`).
Example: `⟨39, 256, .unset⟩` is a map of 39 entries in 256 buckets with no threshold. -/
structure Map where
  count : Nat
  capacity : Nat
  shrinkBelow : ShrinkBelow

/-- The threshold a failed shrink writes down: `(self.count.load(..) / 2).max(1)` in
`try_resize`. It is never 0: a threshold of 0 would let no remove ask for a shrink ever again,
since no count is below 0.
Examples: 39 entries give 19; 3 entries give 1; 1 entry gives 1. -/
def thresholdAfterFailure (count : Nat) : Nat := max (count / 2) 1

/-- Whether a remove that left the map `m` (its count already lowered by one) asks for a
shrink: the test at the end of `unlink_held`, `prev - 1 < table.shrink_at.load(..)`, which
`asks_iff_below_word` proves is these two tests.
Example: 18 entries in 256 buckets with threshold `below 19` ask; 19 entries do not. -/
def AsksShrink (m : Map) : Prop :=
  Underfull m.count m.capacity ∧ m.shrinkBelow.Allows m.count

/-- Lean can compute `AsksShrink`: it is two computable tests joined by "and". -/
instance (m : Map) : Decidable (AsksShrink m) := by
  unfold AsksShrink
  infer_instance

/-- Whether a shrink's copy fits in the half-size table. The model does not place entries, so
the caller chooses (`fits`), with one exception taken from `copy_into`: a map with no entries
always fits, since there is no entry that could fail to find a place.
Example: `CopyFits ⟨0, 256, .unset⟩ false` holds, because the map is empty. -/
def CopyFits (m : Map) (fits : Bool) : Prop :=
  fits = true ∨ m.count = 0

/-- Lean can compute `CopyFits`: it is two equalities joined by "or". -/
instance (m : Map) (fits : Bool) : Decidable (CopyFits m fits) := by
  unfold CopyFits
  infer_instance

/-- A resize that published its new table: the `Some(new_table)` arm of `try_resize`. The
table gets the new capacity and the threshold is erased (the new table starts with its own word,
`Table::new`).
Example: `published ⟨18, 256, .below 19⟩ 128` is `⟨18, 128, .unset⟩`. -/
def published (m : Map) (newCapacity : Nat) : Map :=
  { m with capacity := newCapacity, shrinkBelow := .unset }

/-- A shrink whose copy did not fit, given up: the `None` arm of `try_resize`. The table stays
as it was and the threshold becomes `thresholdAfterFailure` of the count.
Example: `gaveUp ⟨39, 256, .unset⟩` is `⟨39, 256, .below 19⟩`. -/
def gaveUp (m : Map) : Map :=
  { m with shrinkBelow := .below (thresholdAfterFailure m.count) }

/-- The map once a remove has unlinked one entry: `self.count.fetch_sub(1, ..)` in
`unlink_held`. The threshold and the table stay as they were.
Example: `unlinkOne ⟨40, 256, .unset⟩` is `⟨39, 256, .unset⟩`. -/
def unlinkOne (m : Map) : Map :=
  { m with count := m.count - 1 }

/-! ## The operations -/

/-- The operations of the model.
In the code an insert that leaves the table more than three quarters full, or finds no room
near its bucket, grows the table. The model lets a grow come after any operation instead,
which covers those cases and more: a theorem about every sequence of these operations covers
every sequence the code can produce. -/
inductive Op where
  /-- An insert of a key that was absent: `insert_impl` links an entry and `count_in` adds one
  to the count. (An insert that replaces a present key changes neither the count nor the
  threshold, so the model has no step for it.) -/
  | insert
  /-- A remove of a present key: `unlink_held` takes one off the count, then asks for a shrink
  when `AsksShrink` holds. `fits` says whether that shrink's copy would fit. -/
  | remove (fits : Bool)
  /-- A grow, `try_resize(capacity * 2)`. In the model a grow always publishes, as in the
  code, whose loop doubles the new table again until the copy fits. -/
  | grow
  /-- `clear`: every entry removed, the count set to 0 and the threshold erased. -/
  | clear

/-- What one operation did about resizing. The theorems read these. -/
inductive Outcome where
  /-- No resize happened. -/
  | noResize
  /-- A remove asked for a shrink, and its copy fit: the half-size table was published. -/
  | shrunk
  /-- A remove asked for a shrink, and its copy of `count` entries did not fit. -/
  | gaveUp (count : Nat)
  /-- A grow published a table of twice the capacity. -/
  | grown
  /-- A clear ran. -/
  | cleared
  deriving DecidableEq, Repr

/-- The outcomes that erase the threshold: a published resize (a shrink or a grow) and a
clear. -/
def Outcome.Erases : Outcome → Prop
  | .shrunk => True
  | .grown => True
  | .cleared => True
  | _ => False

/-- The outcomes of a remove that asked for a shrink, whether or not it fit. -/
def Outcome.AskedShrink : Outcome → Prop
  | .shrunk => True
  | .gaveUp _ => True
  | _ => False

/-- One operation's result: the map after it, and what it did about resizing. -/
structure Result where
  map : Map
  outcome : Outcome

/-- What a remove does once it unlinked its entry and `left` is the map with one entry fewer:
nothing more when no shrink is asked for; otherwise a shrink to half the capacity, published
when the copy fits and given up when it does not (`try_resize(table.capacity / 2)`). The code's
tables are powers of two of at least 64 buckets and a shrink is asked for only above 64, so
half the capacity is exactly the size `try_resize` builds.
Example: from `⟨39, 256, .unset⟩` with a copy that does not fit, the result is
`⟨39, 256, .below 19⟩` with outcome `gaveUp 39`. -/
def afterUnlink (left : Map) (fits : Bool) : Result :=
  if AsksShrink left then
    if CopyFits left fits then ⟨published left (left.capacity / 2), .shrunk⟩
    else ⟨gaveUp left, .gaveUp left.count⟩
  else ⟨left, .noResize⟩

/-- One operation on the map `m`.
- An insert adds one entry.
- A remove of a map with no entries removes nothing (there is no present key); otherwise it
  unlinks one entry and goes on as `afterUnlink` says.
- A grow publishes a table of twice the capacity.
- A clear empties the map and erases the threshold, keeping the table (`clear` empties the
  current table in place). -/
def step (m : Map) : Op → Result
  | .insert => ⟨{ m with count := m.count + 1 }, .noResize⟩
  | .remove fits => if m.count = 0 then ⟨m, .noResize⟩ else afterUnlink (unlinkOne m) fits
  | .grow => ⟨published m (2 * m.capacity), .grown⟩
  | .clear => ⟨{ m with count := 0, shrinkBelow := .unset }, .cleared⟩

/-- The map after the operations `ops`, done in order from `m`.
Example: `run m []` is `m`. -/
def run (m : Map) : List Op → Map
  | [] => m
  | op :: ops => run (step m op).map ops

/-- The counts of the failed shrinks of a run, in the order they happened.
Example: a run whose shrinks fail at 39 and then at 18 entries gives `[39, 18]`. -/
def failures (m : Map) : List Op → List Nat
  | [] => []
  | op :: ops =>
    match (step m op).outcome with
    | .gaveUp c => c :: failures (step m op).map ops
    | _ => failures (step m op).map ops

/-- No operation of the run erases the threshold: the run lies between two erasures. -/
def NoErasure (m : Map) : List Op → Prop
  | [] => True
  | op :: ops => ¬ (step m op).outcome.Erases ∧ NoErasure (step m op).map ops

/-- A run of inserts and removes only: no grow and no clear. -/
def InsertsAndRemoves (ops : List Op) : Prop :=
  ∀ op ∈ ops, op = .insert ∨ ∃ fits, op = .remove fits

/-- Every operation of the run leaves at least `b` entries.
Example: from 39 entries, "insert, remove, remove" leaves 40, 39, 38, so it stays at least 19. -/
def StaysAtLeast (b : Nat) (m : Map) : List Op → Prop
  | [] => True
  | op :: ops => b ≤ (step m op).map.count ∧ StaysAtLeast b (step m op).map ops

/-- No operation of the run asks for a shrink. -/
def NoShrinkAsked (m : Map) : List Op → Prop
  | [] => True
  | op :: ops => ¬ (step m op).outcome.AskedShrink ∧ NoShrinkAsked (step m op).map ops

/-! ## The three ways a remove can end

Each lemma below names one branch of `afterUnlink`, so the proofs after it can say which
branch they are in instead of unfolding the code again. -/

/-- A remove that asks for no shrink ends with the map it left and no resize.
Example: 19 entries with threshold `below 19` end as they are. -/
theorem afterUnlink_of_not_asks (left : Map) (fits : Bool) (h : ¬ AsksShrink left) :
    afterUnlink left fits = ⟨left, .noResize⟩ := by
  -- The first test of `afterUnlink` is false, so its last line is the result.
  simp [afterUnlink, h]

/-- A remove that asks for a shrink whose copy fits ends with the half-size table published.
Example: 18 entries of 256 buckets that fit end as 18 entries of 128 buckets. -/
theorem afterUnlink_of_fits (left : Map) (fits : Bool) (h : AsksShrink left)
    (hfit : CopyFits left fits) :
    afterUnlink left fits = ⟨published left (left.capacity / 2), .shrunk⟩ := by
  -- Both tests of `afterUnlink` are true, so its first branch is the result.
  simp [afterUnlink, h, hfit]

/-- A remove that asks for a shrink whose copy does not fit ends with the shrink given up.
Example: 39 entries that do not fit end with threshold `below 19` and outcome `gaveUp 39`. -/
theorem afterUnlink_of_not_fits (left : Map) (fits : Bool) (h : AsksShrink left)
    (hfit : ¬ CopyFits left fits) :
    afterUnlink left fits = ⟨gaveUp left, .gaveUp left.count⟩ := by
  -- The first test is true and the second false, so the middle branch is the result.
  simp [afterUnlink, h, hfit]

/-- Unlinking an entry does not touch the threshold: only the count goes down. -/
theorem unlinkOne_shrinkBelow (m : Map) : (unlinkOne m).shrinkBelow = m.shrinkBelow := rfl

/-! ## 1. Every successful resize and every clear erase the threshold -/

/-- A published resize erases the threshold, whatever it was.
Example: a table with threshold `below 19`, once a resize publishes, has no threshold. -/
theorem published_erases (m : Map) (newCapacity : Nat) :
    (published m newCapacity).shrinkBelow = .unset := rfl

/-- A grow erases the threshold. -/
theorem grow_erases (m : Map) : (step m .grow).map.shrinkBelow = .unset := rfl

/-- A clear erases the threshold, and empties the map.
Example: 39 entries with threshold `below 19`, once cleared, are 0 entries with no
threshold. -/
theorem clear_erases (m : Map) :
    (step m .clear).map.shrinkBelow = .unset ∧ (step m .clear).map.count = 0 := ⟨rfl, rfl⟩

/-- Every operation whose outcome is an erasure (a published shrink, a grow, a clear) leaves no
threshold behind. This is item 1 of the file's summary, for every map and every operation. -/
theorem erasure_erases (m : Map) (op : Op) (h : (step m op).outcome.Erases) :
    (step m op).map.shrinkBelow = .unset := by
  cases op with
  | insert =>
    -- An insert's outcome is `noResize`, which is not an erasure: this case cannot happen.
    simp [step, Outcome.Erases] at h
  | grow => rfl
  | clear => rfl
  | remove fits =>
    unfold step at h ⊢
    by_cases h0 : m.count = 0
    · -- An empty map's remove resizes nothing: not an erasure, so this case cannot happen.
      simp [h0, Outcome.Erases] at h
    · -- Otherwise the remove ends in one of the three branches of `afterUnlink`.
      simp only [h0, ite_false] at h ⊢
      by_cases hask : AsksShrink (unlinkOne m)
      · by_cases hfit : CopyFits (unlinkOne m) fits
        · -- The shrink fit and published: `published` erases the threshold.
          rw [afterUnlink_of_fits _ _ hask hfit]
          rfl
        · -- The shrink gave up: `gaveUp` is not an erasure, so this case cannot happen.
          rw [afterUnlink_of_not_fits _ _ hask hfit] at h
          simp [Outcome.Erases] at h
      · -- No shrink was asked for: `noResize` is not an erasure, so this case cannot happen.
        rw [afterUnlink_of_not_asks _ _ hask] at h
        simp [Outcome.Erases] at h

/-! ## What one step does to the threshold

Two facts carry every later proof: a step that resizes nothing keeps the threshold, and a
failed shrink happened at a count the old threshold allowed, never at 0, and writes
`thresholdAfterFailure` of that count. -/

/-- A step whose outcome is `noResize` leaves the threshold as it was.
Example: an insert into a map with threshold `below 19` keeps `below 19`. -/
theorem noResize_keeps (m : Map) (op : Op) (h : (step m op).outcome = .noResize) :
    (step m op).map.shrinkBelow = m.shrinkBelow := by
  cases op with
  | insert => rfl -- an insert changes only the count
  | grow => simp [step] at h -- a grow's outcome is `grown`: this case cannot happen
  | clear => simp [step] at h -- a clear's outcome is `cleared`: this case cannot happen
  | remove fits =>
    unfold step at h ⊢
    by_cases h0 : m.count = 0
    · -- An empty map's remove leaves the map as it was.
      simp [h0]
    · simp only [h0, ite_false] at h ⊢
      by_cases hask : AsksShrink (unlinkOne m)
      · -- A shrink was asked for, so the outcome is `shrunk` or `gaveUp`, never `noResize`:
        -- this case cannot happen.
        by_cases hfit : CopyFits (unlinkOne m) fits
        · rw [afterUnlink_of_fits _ _ hask hfit] at h
          simp at h
        · rw [afterUnlink_of_not_fits _ _ hask hfit] at h
          simp at h
      · -- No shrink was asked for: the map is the one the unlink left, whose threshold is the
        -- old one (`unlinkOne_shrinkBelow`).
        rw [afterUnlink_of_not_asks _ _ hask]
        exact unlinkOne_shrinkBelow m

/-- A step whose outcome is a failed shrink at `c` entries: the old threshold allowed `c`, the
count `c` is at least 1, and the new threshold is `thresholdAfterFailure c`.
Example: a failure at 39 entries under no threshold leaves `below 19`. -/
theorem gaveUp_facts (m : Map) (op : Op) (c : Nat) (h : (step m op).outcome = .gaveUp c) :
    m.shrinkBelow.Allows c ∧ 0 < c ∧
      (step m op).map.shrinkBelow = .below (thresholdAfterFailure c) := by
  cases op with
  | insert => simp [step] at h -- an insert's outcome is `noResize`: cannot happen
  | grow => simp [step] at h -- a grow's outcome is `grown`: cannot happen
  | clear => simp [step] at h -- a clear's outcome is `cleared`: cannot happen
  | remove fits =>
    unfold step at h ⊢
    by_cases h0 : m.count = 0
    · -- An empty map's remove resizes nothing: cannot happen.
      simp [h0] at h
    · simp only [h0, ite_false] at h ⊢
      by_cases hask : AsksShrink (unlinkOne m)
      · by_cases hfit : CopyFits (unlinkOne m) fits
        · -- The shrink fit: the outcome is `shrunk`, not `gaveUp`, so this cannot happen.
          rw [afterUnlink_of_fits _ _ hask hfit] at h
          simp at h
        · -- The shrink gave up at `c`, the count the unlink left.
          rw [afterUnlink_of_not_fits _ _ hask hfit] at h ⊢
          -- Reading the outcome: `c` is that count.
          simp only [Outcome.gaveUp.injEq] at h
          subst h
          refine ⟨?_, ?_, rfl⟩
          · -- The remove asked for the shrink, so the threshold allowed that count; the unlink
            -- did not change the threshold.
            exact hask.2
          · -- The copy did not fit, and an empty map always fits, so the count is not 0.
            unfold CopyFits at hfit
            exact Nat.pos_of_ne_zero (fun hz => hfit (Or.inr hz))
      · -- No shrink was asked for: the outcome is `noResize`, so this cannot happen.
        rw [afterUnlink_of_not_asks _ _ hask] at h
        simp at h

/-! ## 2. After a failed shrink, no retry until half the entries are gone -/

/-- Right after a remove whose shrink failed at `c` entries, the threshold is
`max (c / 2) 1`.
Example: a failure at 39 entries leaves `below 19`. -/
theorem failed_shrink_records (m : Map) (fits : Bool) (c : Nat)
    (h : (step m (.remove fits)).outcome = .gaveUp c) :
    (step m (.remove fits)).map.shrinkBelow = .below (thresholdAfterFailure c) :=
  -- The third of the `gaveUp_facts`.
  (gaveUp_facts m (.remove fits) c h).2.2

/-- With threshold `below b`, a remove of a map with entries asks for a shrink exactly when it
leaves fewer than `b` entries and the map underfull.
Example: with `below 19` in 256 buckets, the remove that leaves 18 asks; the one that leaves
19 does not. -/
theorem remove_asks_iff (m : Map) (fits : Bool) (b : Nat) (hb : m.shrinkBelow = .below b)
    (hc : 0 < m.count) :
    (step m (.remove fits)).outcome.AskedShrink ↔
      (Underfull (m.count - 1) m.capacity ∧ m.count - 1 < b) := by
  -- The map has an entry, so the remove unlinks one and goes on to `afterUnlink`.
  have h0 : m.count ≠ 0 := Nat.pos_iff_ne_zero.mp hc
  simp only [step, h0, ite_false]
  -- After the unlink, `AsksShrink` reads exactly "underfull and below `b`".
  have hask : AsksShrink (unlinkOne m) ↔ (Underfull (m.count - 1) m.capacity ∧ m.count - 1 < b) := by
    simp [AsksShrink, unlinkOne, hb, ShrinkBelow.Allows]
  by_cases h : AsksShrink (unlinkOne m)
  · -- It asked: the outcome is `shrunk` or `gaveUp`, both an asked shrink, and the right side
    -- holds by `hask`.
    by_cases hfit : CopyFits (unlinkOne m) fits
    · rw [afterUnlink_of_fits _ _ h hfit]
      exact ⟨fun _ => hask.mp h, fun _ => trivial⟩
    · rw [afterUnlink_of_not_fits _ _ h hfit]
      exact ⟨fun _ => hask.mp h, fun _ => trivial⟩
  · -- It did not ask: the outcome is `noResize`, not an asked shrink, and the right side fails
    -- by `hask`.
    rw [afterUnlink_of_not_asks _ _ h]
    exact ⟨fun hn => absurd hn id, fun hr => absurd (hask.mpr hr) h⟩

/-- With threshold `below b`, an operation of a run of inserts and removes that leaves at least
`b` entries asks for no shrink.
Example: with `below 19`, a remove from 40 entries (leaving 39) asks for nothing. -/
theorem no_ask_at_or_above (m : Map) (op : Op) (b : Nat) (hb : m.shrinkBelow = .below b)
    (hop : op = .insert ∨ ∃ fits, op = .remove fits) (hstay : b ≤ (step m op).map.count) :
    ¬ (step m op).outcome.AskedShrink := by
  rcases hop with rfl | ⟨fits, rfl⟩
  · -- An insert never asks for a shrink.
    simp [step, Outcome.AskedShrink]
  · by_cases h0 : m.count = 0
    · -- An empty map's remove resizes nothing.
      simp [step, h0, Outcome.AskedShrink]
    · -- The remove asks only when it leaves fewer than `b` entries (`remove_asks_iff`). The
      -- count it leaves is at least `b` here, so it does not ask.
      have hc : 0 < m.count := Nat.pos_of_ne_zero h0
      rw [remove_asks_iff m fits b hb hc]
      intro hr
      -- If it asked, its map would be the half-size table or the given-up one; either way its
      -- count is `m.count - 1`, at least `b` by `hstay`, against `m.count - 1 < b`.
      have hcount : (step m (.remove fits)).map.count = m.count - 1 := by
        simp only [step, h0, ite_false]
        by_cases hask : AsksShrink (unlinkOne m)
        · by_cases hfit : CopyFits (unlinkOne m) fits
          · rw [afterUnlink_of_fits _ _ hask hfit]; rfl
          · rw [afterUnlink_of_not_fits _ _ hask hfit]; rfl
        · rw [afterUnlink_of_not_asks _ _ hask]; rfl
      -- `b ≤ m.count - 1` and `m.count - 1 < b` cannot both hold.
      omega

/-- With threshold `below b`, a run of inserts and removes that never leaves fewer than `b`
entries asks for no shrink, and ends with the threshold still `below b`.
Example: with `below 19`, inserting and removing between 39 and 40 entries for a million
operations asks for nothing and keeps `below 19`. -/
theorem no_shrink_while_at_least (m : Map) (b : Nat) (ops : List Op)
    (hb : m.shrinkBelow = .below b) (hops : InsertsAndRemoves ops)
    (hstay : StaysAtLeast b m ops) :
    NoShrinkAsked m ops ∧ (run m ops).shrinkBelow = .below b := by
  induction ops generalizing m with
  | nil =>
    -- An empty run asks for nothing and leaves the map as it was.
    exact ⟨trivial, hb⟩
  | cons op ops ih =>
    -- The first operation is an insert or a remove, and it leaves at least `b` entries.
    have hop : op = .insert ∨ ∃ fits, op = .remove fits := hops op (List.mem_cons_self ..)
    have hfirst : b ≤ (step m op).map.count := hstay.1
    -- So it asks for no shrink (`no_ask_at_or_above`).
    have hno : ¬ (step m op).outcome.AskedShrink := no_ask_at_or_above m op b hb hop hfirst
    -- An insert or a remove that asks for no shrink resizes nothing, so its outcome is
    -- `noResize` and it keeps the threshold `below b` (`noResize_keeps`).
    have hquiet : (step m op).outcome = .noResize := by
      rcases hop with rfl | ⟨fits, rfl⟩
      · rfl
      · simp only [step] at hno ⊢
        by_cases h0 : m.count = 0
        · simp [h0]
        · simp only [h0, ite_false] at hno ⊢
          by_cases hask : AsksShrink (unlinkOne m)
          · by_cases hfit : CopyFits (unlinkOne m) fits
            · rw [afterUnlink_of_fits _ _ hask hfit] at hno
              exact absurd trivial hno
            · rw [afterUnlink_of_not_fits _ _ hask hfit] at hno
              exact absurd trivial hno
          · rw [afterUnlink_of_not_asks _ _ hask]
    have hb' : (step m op).map.shrinkBelow = .below b := (noResize_keeps m op hquiet).trans hb
    -- The rest of the run starts from that map, with the same threshold: by induction it
    -- asks for nothing and keeps `below b`.
    have hrest := ih (step m op).map hb'
      (fun op' hmem => hops op' (List.mem_cons_of_mem _ hmem)) hstay.2
    exact ⟨⟨hno, hrest.1⟩, hrest.2⟩

/-- With threshold `below b`, the first remove that leaves fewer than `b` entries while the map
is underfull asks for a shrink.
Example: with `below 19` in 256 buckets, the remove from 19 entries (leaving 18) asks. -/
theorem first_remove_below_asks (m : Map) (fits : Bool) (b : Nat)
    (hb : m.shrinkBelow = .below b) (hc : 0 < m.count) (hlow : m.count - 1 < b)
    (hu : Underfull (m.count - 1) m.capacity) :
    (step m (.remove fits)).outcome.AskedShrink :=
  -- The right side of `remove_asks_iff` holds.
  (remove_asks_iff m fits b hb hc).mpr ⟨hu, hlow⟩

/-- Item 2 of the file's summary, in one statement. After a remove whose shrink failed at `c`
entries, take any run of inserts and removes that never leaves fewer than `max (c / 2) 1`
entries. That run asks for no shrink. And at its end, a remove that leaves fewer than
`max (c / 2) 1` entries while the map is underfull asks for a shrink.
Example: a failure at 39 entries; any churn that stays at 19 entries or more asks for
nothing; then the remove that leaves 18 entries in a table of 256 buckets asks. -/
theorem after_failed_shrink (m : Map) (fits : Bool) (c : Nat) (ops : List Op)
    (hfail : (step m (.remove fits)).outcome = .gaveUp c)
    (hops : InsertsAndRemoves ops)
    (hstay : StaysAtLeast (thresholdAfterFailure c) (step m (.remove fits)).map ops) :
    NoShrinkAsked (step m (.remove fits)).map ops ∧
      ∀ fits' : Bool,
        let last := run (step m (.remove fits)).map ops
        0 < last.count → last.count - 1 < thresholdAfterFailure c →
          Underfull (last.count - 1) last.capacity →
          (step last (.remove fits')).outcome.AskedShrink := by
  -- The failed shrink wrote `below (max (c / 2) 1)` (`failed_shrink_records`).
  have hrec := failed_shrink_records m fits c hfail
  -- During the run it stays so and nothing is asked (`no_shrink_while_at_least`).
  have hrun := no_shrink_while_at_least _ _ ops hrec hops hstay
  refine ⟨hrun.1, ?_⟩
  intro fits' last hc hlow hu
  -- At the end the threshold is still `below (max (c / 2) 1)`, so the first remove below it
  -- asks (`first_remove_below_asks`).
  exact first_remove_below_asks _ fits' _ hrun.2 hc hlow hu

/-- With no threshold (after a clear, say), a remove of a map with entries asks for a shrink
exactly when it leaves the map underfull: nothing blocks it.
Example: after a clear and 30 inserts into 256 buckets, the remove that leaves 29 asks
(4 * 29 = 116 is less than 256). -/
theorem unset_remove_asks_iff (m : Map) (fits : Bool) (hb : m.shrinkBelow = .unset)
    (hc : 0 < m.count) :
    (step m (.remove fits)).outcome.AskedShrink ↔ Underfull (m.count - 1) m.capacity := by
  have h0 : m.count ≠ 0 := Nat.pos_iff_ne_zero.mp hc
  simp only [step, h0, ite_false]
  -- With no threshold, `AsksShrink` after the unlink is "underfull" alone.
  have hask : AsksShrink (unlinkOne m) ↔ Underfull (m.count - 1) m.capacity := by
    simp [AsksShrink, unlinkOne, hb, ShrinkBelow.Allows]
  by_cases h : AsksShrink (unlinkOne m)
  · -- It asked: `shrunk` or `gaveUp`, and the map is underfull by `hask`.
    by_cases hfit : CopyFits (unlinkOne m) fits
    · rw [afterUnlink_of_fits _ _ h hfit]
      exact ⟨fun _ => hask.mp h, fun _ => trivial⟩
    · rw [afterUnlink_of_not_fits _ _ h hfit]
      exact ⟨fun _ => hask.mp h, fun _ => trivial⟩
  · -- It did not ask: `noResize`, and the map is not underfull by `hask`.
    rw [afterUnlink_of_not_asks _ _ h]
    exact ⟨fun hn => absurd hn id, fun hr => absurd (hask.mpr hr) h⟩

/-! ## 3. The work bound -/

/-- Each number of the list is less than half the one before it (halves rounded down).
Example: `[39, 18, 8, 3]` is halving (18 < 19, 8 < 9, 3 < 4); `[39, 19]` is not. -/
def Halving : List Nat → Prop
  | a :: b :: rest => b < a / 2 ∧ Halving (b :: rest)
  | _ => True

/-- `Descending t cs`: the counts `cs`, read in order, are each allowed by the threshold the one
before wrote (the first one by `t`), and each is at least 1. This is what the failed shrinks
of a run with no erasure look like (`failures_descending`).
Example: `Descending .unset [39, 18]` holds: 39 is allowed by no threshold, 18 by `below 19`. -/
def Descending : ShrinkBelow → List Nat → Prop
  | _, [] => True
  | t, c :: cs => t.Allows c ∧ 0 < c ∧ Descending (.below (thresholdAfterFailure c)) cs

/-- The failed shrinks of a run with no erasure are `Descending`, starting from the threshold
the run starts with.
In plain words: between two erasures, each failed shrink was allowed by the threshold the one
before it wrote down. -/
theorem failures_descending (m : Map) (ops : List Op) (h : NoErasure m ops) :
    Descending m.shrinkBelow (failures m ops) := by
  induction ops generalizing m with
  | nil =>
    -- No operation, no failure: the empty list is `Descending`.
    trivial
  | cons op ops ih =>
    -- The rest of the run starts from the map after `op`, with no erasure either.
    have hrest := ih (step m op).map h.2
    -- Look at what `op` did.
    unfold failures
    cases hout : (step m op).outcome with
    | gaveUp c =>
      -- `op` was a failed shrink at `c`: the old threshold allowed `c`, `c` is at least 1, and
      -- the threshold the rest starts from is `thresholdAfterFailure c` (`gaveUp_facts`).
      obtain ⟨hallow, hpos, hnew⟩ := gaveUp_facts m op c hout
      rw [hnew] at hrest
      exact ⟨hallow, hpos, hrest⟩
    | noResize =>
      -- `op` resized nothing: it kept the threshold (`noResize_keeps`), so the rest's
      -- failures are `Descending` from the same threshold.
      rw [noResize_keeps m op hout] at hrest
      exact hrest
    | shrunk =>
      -- An erasure: excluded by `NoErasure`.
      exact absurd (by rw [hout]; trivial) h.1
    | grown =>
      exact absurd (by rw [hout]; trivial) h.1
    | cleared =>
      exact absurd (by rw [hout]; trivial) h.1

/-- The step from one failed shrink to the next: a count `b` that is at least 1 and allowed by
the threshold a failure at `a` wrote is less than half of `a`.
Example: after a failure at 39 (threshold 19), the next can be at 18 at most, and 18 < 19.
Why: `b < max (a / 2) 1` and `1 ≤ b` force `max (a / 2) 1` to be at least 2, so it is `a / 2`
itself, and `b < a / 2`. -/
theorem next_below_half (a b : Nat)
    (hallow : (ShrinkBelow.below (thresholdAfterFailure a)).Allows b) (hpos : 0 < b) :
    b < a / 2 := by
  -- `Allows` here reads `b < max (a / 2) 1`.
  simp only [ShrinkBelow.Allows, thresholdAfterFailure] at hallow
  -- Linear arithmetic over the natural numbers (`omega`) with the two facts above: if
  -- `a / 2` were 0, the maximum would be 1 and `b < 1` would contradict `0 < b`.
  omega

/-- Failed shrinks that are `Descending` are `Halving`.
In plain words: each failed shrink happens at fewer than half the entries of the one before. -/
theorem descending_halving (t : ShrinkBelow) (cs : List Nat) (h : Descending t cs) :
    Halving cs := by
  induction cs generalizing t with
  | nil => trivial
  | cons a rest ih =>
    -- The tail is `Descending` from the threshold `a` wrote, so it is `Halving` by induction.
    have htail : Halving rest := ih _ h.2.2
    cases rest with
    | nil => trivial -- one number alone is halving
    | cons b rest' =>
      -- The next count `b` is allowed by `a`'s threshold and at least 1, so `b < a / 2`
      -- (`next_below_half`).
      exact ⟨next_below_half a b h.2.2.1 h.2.2.2.1, htail⟩

/-- The total of a `Descending` list is less than twice its first number.
Example: `39 + 18 + 8 + 3 = 68`, less than `2 * 39 = 78`.
Why: each number is at most half the one before, minus one, so the total stays below
`a + a / 2 + a / 4 + ...`, which never reaches `2 * a`. The proof shows that the total of a
list starting at `a` is below `2 * a`: true for `[a]` since `a ≥ 1`, and adding a new first
number `a` in front of a list starting at `b < a / 2` adds `a` to a total below `2 * b`, which
is at most `a`. -/
theorem descending_total (t : ShrinkBelow) (a : Nat) (rest : List Nat)
    (h : Descending t (a :: rest)) : (a :: rest).sum < 2 * a := by
  induction rest generalizing t a with
  | nil =>
    -- The total of `[a]` is `a`, below `2 * a` because `a` is at least 1.
    have hpos : 0 < a := h.2.1
    simp only [List.sum_cons, List.sum_nil]
    omega
  | cons b rest' ih =>
    -- The list after `a` starts at `b` and is `Descending` from `a`'s threshold, so its total
    -- is below `2 * b` (induction).
    have htail : (b :: rest').sum < 2 * b := ih _ b h.2.2
    -- And `b < a / 2` (`next_below_half`), so `2 * b` is less than `a`.
    have hb : b < a / 2 := next_below_half a b h.2.2.1 h.2.2.2.1
    -- The whole total is `a` plus the tail's: below `a + 2 * b`, at most `2 * a`
    -- (linear arithmetic, `omega`, with `htail` and `hb`).
    rw [List.sum_cons]
    omega

/-- Item 3 of the file's summary, first half: between two erasures, each failed shrink happens
at fewer than half the entries of the one before.
Example: failures at 39, then 18, then 8 are possible; failures at 39 and then 19 are not. -/
theorem failed_shrinks_halve (m : Map) (ops : List Op) (h : NoErasure m ops) :
    Halving (failures m ops) :=
  descending_halving _ _ (failures_descending m ops h)

/-- Item 3 of the file's summary, second half, the work bound: between two erasures, if the
first failed shrink happened at `c` entries, all the failed shrinks together happened at fewer
than `2 * c` entries in total. A failed shrink of `n` entries clones at most `n` of them
(`copy_into` clones each entry it meets, the one that does not fit included, and stops there),
so the failed shrinks of any such run clone fewer than `2 * c` entries in total.
Example: a first failure at 39 entries; however the run goes on, its failed shrinks clone
fewer than 78 entries in total (at most 39 + 18 + 8 + 3 = 68). For contrast, the code before
the fix, which this file does not model, cloned up to 39 entries on every remove of 39
entries churned by one insert and one remove at a time. -/
theorem failed_shrink_copies_below_twice_first (m : Map) (ops : List Op) (h : NoErasure m ops)
    (c : Nat) (rest : List Nat) (hfirst : failures m ops = c :: rest) :
    (failures m ops).sum < 2 * c := by
  -- The failures are `Descending` (`failures_descending`), and a `Descending` list totals
  -- less than twice its first number (`descending_total`).
  have hd := failures_descending m ops h
  rw [hfirst] at hd ⊢
  exact descending_total _ c rest hd

/-! ## The one word the code keeps

The code keeps no field of its own for the threshold. It folds the threshold and the
quarter-full test into one word of the current table, `Table::shrink_at`
(`kovan-map/src/hopscotch/table.rs`), so a remove makes one compare at the end of `unlink_held`:
`prev - 1 < table.shrink_at.load(..)`. A new table's word starts at `shrink_at` of its capacity
(`Table::new`), a failed shrink lowers it to the smaller of that and the threshold it writes
(`try_resize`), and a clear sets it back (`clear`). Keeping it in the table is the same as keeping
it in the map: only the current table is ever unlinked from (a replaced table keeps its writer
guards held), and a new table starts with no failed shrink, just as a publication erases the
threshold here.

`word` computes that word from the model's map. The theorems prove that the one compare asks for
a shrink exactly when the model's two tests do, and that each write leaves the word the model's
state describes, so every theorem above holds of the code as it is written.
-/

/-- `shrink_at` in `kovan-map/src/hopscotch.rs`: where a new table's word starts. A quarter of
the buckets, rounded up, so that a count below it is exactly a table less than a quarter full;
zero for a table of at most 64 buckets, which never shrinks.
Examples: `shrinkAt 256 = 64`, since `(256 + 3) / 4 = 64`; `shrinkAt 64 = 0`. -/
def shrinkAt (capacity : Nat) : Nat :=
  if minCapacity < capacity then (capacity + 3) / 4 else 0

/-- The word `Table::shrink_at` holds for the map `m`: the table's quarter, lowered to the
threshold when a failed shrink wrote one.
Examples: `word ⟨39, 256, .unset⟩ = 64`; `word ⟨39, 256, .below 19⟩ = 19`. -/
def word (m : Map) : Nat :=
  match m.shrinkBelow with
  | .unset => shrinkAt m.capacity
  | .below n => min (shrinkAt m.capacity) n

/-- A count below the quarter rounded up is exactly a table less than a quarter full: `count <
(capacity + 3) / 4` and `4 * count < capacity` say the same thing about whole numbers.
Example: in 256 buckets both hold for 63 entries and fail for 64. -/
theorem lt_shrinkAt_iff (count capacity : Nat) :
    count < shrinkAt capacity ↔ Underfull count capacity := by
  -- Open both definitions; `split` takes the two cases of the table's size: above 64 buckets
  -- both sides are about a quarter, at most 64 both are false; `omega` settles the arithmetic.
  unfold shrinkAt Underfull
  split <;> omega

/-- The fold is exact: the code's one compare asks for a shrink exactly when the model's two
tests (underfull, and below the threshold if there is one) do.
Example: 18 entries in 256 buckets with threshold 19: the word is `min 64 19 = 19`, and
`18 < 19`; the model asks too, since 18 underfills 256 and is below 19. -/
theorem asks_iff_below_word (m : Map) : AsksShrink m ↔ m.count < word m := by
  -- Open the two definitions and take the two cases of the threshold.
  unfold AsksShrink word
  cases m.shrinkBelow with
  -- No threshold: the model's second test always passes, and the word is the quarter, so both
  -- sides are "underfull" (`lt_shrinkAt_iff`).
  | unset => simp [ShrinkBelow.Allows, lt_shrinkAt_iff]
  -- A threshold `n`: being below the smaller of two numbers is being below both
  -- (`Nat.lt_min`), and below the quarter is underfull (`lt_shrinkAt_iff`).
  | below n => simp [ShrinkBelow.Allows, lt_shrinkAt_iff, Nat.lt_min]

/-- A failed shrink leaves the word the code writes: the smaller of the table's quarter and the
threshold, `shrink_at(capacity).min(failed_at)` in `try_resize`.
Example: a failure at 39 entries in 256 buckets leaves `min 64 19 = 19`. -/
theorem word_gaveUp (m : Map) :
    word (gaveUp m) = min (shrinkAt m.capacity) (thresholdAfterFailure m.count) :=
  -- `gaveUp` keeps the capacity and writes `below` the threshold: `word` computes it directly.
  rfl

/-- A published table's word is its quarter, as `Table::new` makes it.
Example: a shrink to 128 buckets publishes a table whose word is 32. -/
theorem word_published (m : Map) (capacity : Nat) :
    word (published m capacity) = shrinkAt capacity :=
  -- `published` erases the threshold, so the word is the new table's quarter.
  rfl

/-- A clear sets the word back to the table's quarter, as `clear` does.
Example: a clear of a 256-bucket map whose word was 19 leaves 64. -/
theorem word_cleared (m : Map) : word (step m .clear).map = shrinkAt m.capacity :=
  -- A clear keeps the table and erases the threshold, so the word is that table's quarter.
  rfl

end Kovan.HopscotchShrink
