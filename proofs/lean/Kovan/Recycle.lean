/-!
# Recycling retired nodes: the fresh stamp keeps every reader covered

This file checks why `retire_reclaimable` (`kovan/src/reclaim.rs`, `kovan/src/guard.rs`) can hand
a retired node back to a pool and let a structure publish it again: a node a reader still holds
is never freed into the pool, provided the structure re-initialises the node's header with
`RetiredNode::new()` before it publishes the node again. It also shows that the write is
required: a header left as the pool wrote it can let a batch be freed under a reader.

## The story in plain words

Every node carries a birth epoch in its header. `RetiredNode::new()` stamps it from the epoch the
thread last saw, which is never later than the global epoch, before the node is published.

A reader publishes a reservation (the epoch it read), then loads a node. `protect_load` keeps the
load only if the global epoch has not moved since the reservation was published; otherwise it
raises the reservation and loads again. So a reader that holds a node has a reservation equal to
the epoch at the load, and the node, published before the load, was born no later than that.

When nodes retire together they form a batch, and the batch keeps the smallest birth of its
nodes (the head node's birth is lowered to it in place). The reclaimer skips every reservation
older than that smallest birth: such a reader cannot hold a node of the batch, since every node
of it was born after the reservation. Every other reservation covers the batch, and the batch is
freed only once those readers have let go. A reader holding a node is therefore always covered,
and never sees the node freed.

Recycling puts a freed node back into a pool, and a later publication takes it out. If the
structure re-initialises the header, the node is born again at a current epoch and the story
above holds for its new life. If it does not, the header keeps whatever the pool wrote there
(`dealloc` owns the whole allocation, the header included), and a birth later than the global
epoch lets a reader load the node at an older epoch than its birth. The batch then skips that
reader, and is freed while the reader holds the node: the use after free the reclamation model's
`RC_mut_stale_link_birth` configuration finds.

## What the model leaves out

One whole operation runs at a time; the TLA+ model in `proofs/tla/reclaim` checks the concurrent
steps of the same rules (the reservation and its raise, the placement of a batch into the
reservations it does not skip, the traversals, the incarnations a recycled node goes through).
Here a reader holds at most one node, a free names one node of a batch whose covering readers
have let go, and the epoch the stamp reads is any epoch not later than the global one. Nodes and
readers are numbers.
-/

namespace Kovan.Recycle

/-! ## The state -/

/-- Where a node object is in the cycle the pool makes.
Example: a node the structure has just published is `live`. -/
inductive NodeState where
  /-- Published: a reader can load it. -/
  | live
  /-- Retired through kovan: unlinked, waiting for the readers that may hold it. -/
  | retired
  /-- Its `dealloc` ran: the value is dropped and the node waits in the pool. -/
  | pooled
  deriving DecidableEq, Repr

/-- What the model knows. Every node starts in the pool (an allocation the structure has not
made yet is as good as a pooled one), no reader has a reservation, and the epoch is 0.
Example: `{}` is that starting state. -/
structure St where
  /-- Where each node is. -/
  state : Nat → NodeState := fun _ => .pooled
  /-- Each node's header word `birth_epoch`. For a pooled node it is whatever the pool left. -/
  birth : Nat → Nat := fun _ => 0
  /-- The smallest birth of the batch each retired node was retired in: the reclaimer skips every
  reservation older than it. -/
  batchMin : Nat → Nat := fun _ => 0
  /-- Each reader's published reservation, if it is pinned. -/
  res : Nat → Option Nat := fun _ => none
  /-- The node each reader holds, if any: a pointer it loaded under its current guard. -/
  holds : Nat → Option Nat := fun _ => none
  /-- The global epoch. It only grows. -/
  now : Nat := 0

/-- The starting state. -/
def fresh : St := {}

/-- The smallest of a list of numbers; 0 for an empty list, which no retire forms.
Example: `minOf [5, 3, 8] = 3`. -/
def minOf : List Nat → Nat
  | [] => 0
  | [n] => n
  | n :: ns => min n (minOf ns)

/-- The smallest of a non-empty list is at most each member.
Example: `minOf [5, 3, 8] ≤ 8`. -/
theorem minOf_le (l : List Nat) (m : Nat) (hm : m ∈ l) : minOf l ≤ m := by
  -- By induction on the list: the smallest of `n :: ns` is at most `n` and at most the smallest
  -- of `ns`, which the induction hypothesis bounds by every member of `ns`.
  induction l with
  | nil => exact absurd hm (List.not_mem_nil)
  | cons n ns ih =>
    cases ns with
    | nil =>
      -- One member: it is the smallest.
      simp only [List.mem_singleton] at hm
      subst hm
      simp [minOf]
    | cons n' ns' =>
      -- Two or more: either `m` is the first, or it is in the rest.
      simp only [minOf]
      rcases List.mem_cons.mp hm with h | h
      · subst h; exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (ih h)

/-! ## The operations, each mapped to the code -/

/-- One whole operation.
Example: `.take 3 2` takes node 3 from the pool and stamps it born at epoch 2. -/
inductive Op where
  /-- The global epoch advances (`advance_epoch`). -/
  | tick
  /-- A structure takes node `n` from its pool, re-initialises the header with
  `RetiredNode::new()`, which stamps birth `b` (the thread's cached epoch, never later than the
  global one), and publishes the node. -/
  | take (n b : Nat)
  /-- The mutation: a take that publishes node `n` without the fresh header, so its birth is
  `junk`, whatever the pool wrote over it. -/
  | takeStale (n junk : Nat)
  /-- Reader `r` pins: it publishes the current epoch as its reservation (`pin`). -/
  | pin (r : Nat)
  /-- Reader `r` raises its reservation to the current epoch (`protect_load` after it saw the
  epoch move). -/
  | raise (r : Nat)
  /-- Reader `r` loads node `n` (`protect_load`): kept only if `n` is published and the epoch has
  not moved since the reservation, so the reservation is the current epoch. -/
  | load (r n : Nat)
  /-- Reader `r` drops its guard: no reservation, nothing held. -/
  | unpin (r : Nat)
  /-- The structure retires the published nodes `ns` together (`retire_reclaimable`): they form a
  batch whose smallest birth each of them records, and the head node's birth is lowered to it in
  place (`try_retire`). -/
  | retire (ns : List Nat)
  /-- The reclaimer frees retired node `n` into the pool (`free_batch_list`, then
  `Reclaimable::dealloc`): allowed once every reader that holds it is skipped by its batch, that
  is, has a reservation older than the batch's smallest birth. A reader whose reservation covers
  the batch keeps it from being freed. -/
  | free (n : Nat)

/-- Whether reader `r` is skipped by a batch of smallest birth `m`: its reservation is older than
`m`. The free below may run under a skipped reader; the protection rests on such a reader holding
no node of the batch. -/
def Skipped (s : St) (r m : Nat) : Prop :=
  ∃ e, s.res r = some e ∧ e < m

/-- The free's condition: every reader holding `n` is skipped by `n`'s batch. -/
def MayFree (s : St) (n : Nat) : Prop :=
  s.state n = .retired ∧ ∀ r, s.holds r = some n → Skipped s r (s.batchMin n)

/-- One operation. An operation whose condition fails changes nothing, as a code path that does
not apply does nothing. The `free` condition is a proposition, so the step takes it as given; the
other conditions are tests on the state. -/
noncomputable def step (s : St) : Op → St
  | .tick => { s with now := s.now + 1 }
  | .take n b =>
    if s.state n = .pooled ∧ b ≤ s.now then
      { s with state := fun m => if m = n then .live else s.state m,
               birth := fun m => if m = n then b else s.birth m }
    else s
  | .takeStale n junk =>
    if s.state n = .pooled then
      { s with state := fun m => if m = n then .live else s.state m,
               birth := fun m => if m = n then junk else s.birth m }
    else s
  | .pin r => { s with res := fun q => if q = r then some s.now else s.res q,
                       holds := fun q => if q = r then none else s.holds q }
  | .raise r =>
    if (s.res r).isSome then { s with res := fun q => if q = r then some s.now else s.res q }
    else s
  | .load r n =>
    if s.state n = .live ∧ s.res r = some s.now then
      { s with holds := fun q => if q = r then some n else s.holds q }
    else s
  | .unpin r => { s with res := fun q => if q = r then none else s.res q,
                         holds := fun q => if q = r then none else s.holds q }
  | .retire ns =>
    let live := ns.filter (fun m => s.state m = .live)
    match live with
    | [] => s
    | head :: _ =>
      let low := minOf (live.map s.birth)
      { s with state := fun m => if m ∈ live then .retired else s.state m,
               batchMin := fun m => if m ∈ live then low else s.batchMin m,
               birth := fun m => if m = head then low else s.birth m }
  | .free n =>
    open Classical in
    if MayFree s n then { s with state := fun m => if m = n then .pooled else s.state m } else s

/-- The state after the operations `ops`, in order. -/
noncomputable def run (s : St) : List Op → St
  | [] => s
  | op :: ops => run (step s op) ops

/-- An operation that is not the mutation. -/
def Op.Fresh : Op → Prop
  | .takeStale _ _ => False
  | _ => True

/-! ## The invariant -/

/-- What every state reachable with fresh takes satisfies.
Example: in the starting state all four facts hold, since no node is published and no reader
holds anything. -/
structure Good (s : St) : Prop where
  /-- A published node was born no later than the global epoch: the stamp reads an epoch already
  reached, and the epoch only grows. -/
  liveBorn : ∀ n, s.state n = .live → s.birth n ≤ s.now
  /-- A reader holds a node only while pinned, at a reservation no later than the global epoch. -/
  holderPinned : ∀ r n, s.holds r = some n → ∃ e, s.res r = some e ∧ e ≤ s.now
  /-- A reader holding a published node has a reservation no older than its birth. -/
  liveCovered : ∀ r n e, s.holds r = some n → s.res r = some e → s.state n = .live →
    s.birth n ≤ e
  /-- A reader holding a retired node has a reservation no older than its batch's smallest
  birth: the batch does not skip it. -/
  retiredCovered : ∀ r n e, s.holds r = some n → s.res r = some e → s.state n = .retired →
    s.batchMin n ≤ e
  /-- No reader holds a pooled node: no use after free. -/
  noUseAfterFree : ∀ r n, s.holds r = some n → s.state n ≠ .pooled

/-- The starting state is good: nothing is published, nobody is pinned. -/
theorem fresh_good : Good fresh where
  -- Every node is pooled and no reader holds or reserves anything, so each fact is about none.
  liveBorn := by intro n h; simp [fresh] at h
  holderPinned := by intro r n h; simp [fresh] at h
  liveCovered := by intro r n e h; simp [fresh] at h
  retiredCovered := by intro r n e h; simp [fresh] at h
  noUseAfterFree := by intro r n h; simp [fresh] at h

/-! ## Every fresh operation keeps the invariant -/

/-- A `tick` keeps every fact: births and reservations stay where they were, below a larger
epoch. -/
theorem tick_good (s : St) (g : Good s) : Good (step s .tick) := by
  constructor
  · -- A published node's birth was at most the old epoch, so at most the new one.
    intro n h; exact Nat.le_succ_of_le (g.liveBorn n h)
  · -- A holder's reservation was at most the old epoch, so at most the new one.
    intro r n h
    obtain ⟨e, he, hle⟩ := g.holderPinned r n h
    exact ⟨e, he, Nat.le_succ_of_le hle⟩
  · -- Nothing held, reserved or published changed.
    exact g.liveCovered
  · exact g.retiredCovered
  · exact g.noUseAfterFree

/-- A fresh `take` keeps every fact: the node was pooled, so no reader held it, and it is born no
later than the epoch. -/
theorem take_good (s : St) (g : Good s) (n b : Nat) : Good (step s (.take n b)) := by
  -- When the take's condition fails, nothing changes.
  by_cases hc : s.state n = .pooled ∧ b ≤ s.now
  case neg => simp only [step, hc, ite_false]; exact g
  case pos =>
  simp only [step, hc, and_self, ite_true]
  -- No reader holds `n`: it was pooled.
  have nobody : ∀ r, s.holds r ≠ some n := fun r h => g.noUseAfterFree r n h hc.1
  constructor
  · -- `n` is born at `b`, at most the epoch; every other node is as it was.
    intro m h
    by_cases hm : m = n
    · simp [hm]; exact hc.2
    · simp [hm] at h ⊢; exact g.liveBorn m h
  · exact g.holderPinned
  · -- A holder of a published node does not hold `n`, so that node's birth is unchanged.
    intro r m e h he hl
    by_cases hm : m = n
    · exact absurd (hm ▸ h) (nobody r)
    · simp [hm] at hl ⊢; exact g.liveCovered r m e h he hl
  · -- `n` is published, not retired; every other node is as it was.
    intro r m e h he hl
    by_cases hm : m = n
    · simp [hm] at hl
    · simp [hm] at hl; exact g.retiredCovered r m e h he hl
  · -- `n` is published; every other node is as it was.
    intro r m h
    by_cases hm : m = n
    · simp [hm]
    · simp [hm]; exact g.noUseAfterFree r m h

/-- A `pin` keeps every fact: the reader holds nothing afterwards, and nobody else changed. -/
theorem pin_good (s : St) (g : Good s) (r : Nat) : Good (step s (.pin r)) := by
  simp only [step]
  constructor
  · -- Births and the epoch are as they were.
    exact g.liveBorn
  · -- The pinned reader holds nothing; every other reader is as it was.
    intro q n h
    by_cases hq : q = r
    · simp [hq] at h
    · simp [hq] at h ⊢; exact g.holderPinned q n h
  · -- The same for a held published node: only other readers hold one, unchanged.
    intro q n e h he hl
    by_cases hq : q = r
    · simp [hq] at h
    · simp [hq] at h he; exact g.liveCovered q n e h he hl
  · -- And for a held retired node.
    intro q n e h he hl
    by_cases hq : q = r
    · simp [hq] at h
    · simp [hq] at h he; exact g.retiredCovered q n e h he hl
  · -- No state changed, and the reader holds nothing: still no held pooled node.
    intro q n h
    by_cases hq : q = r
    · simp [hq] at h
    · simp [hq] at h; exact g.noUseAfterFree q n h

/-- A `raise` keeps every fact: the reader's node was born, and its batch's smallest birth was,
no later than the old reservation, which was no later than the epoch the raise reads. -/
theorem raise_good (s : St) (g : Good s) (r : Nat) : Good (step s (.raise r)) := by
  by_cases hc : (s.res r).isSome
  case neg => simp only [step, hc]; exact g
  case pos =>
  simp only [step, hc, ite_true]
  constructor
  · exact g.liveBorn
  · -- The raised reservation is the epoch itself; the others are as they were.
    intro q n h
    by_cases hq : q = r
    · exact ⟨s.now, by simp [hq], Nat.le_refl _⟩
    · obtain ⟨e, he, hle⟩ := g.holderPinned q n h
      exact ⟨e, by simp [hq, he], hle⟩
  · -- A published node's birth is at most the epoch (`liveBorn`).
    intro q n e h he hl
    by_cases hq : q = r
    · simp [hq] at he; subst he; exact g.liveBorn n hl
    · simp [hq] at he; exact g.liveCovered q n e h he hl
  · -- The batch's smallest birth was at most the old reservation, at most the epoch.
    intro q n e h he hl
    by_cases hq : q = r
    · simp [hq] at he; subst he
      obtain ⟨e0, he0, hle⟩ := g.holderPinned q n h
      exact Nat.le_trans (g.retiredCovered q n e0 h he0 hl) hle
    · simp [hq] at he; exact g.retiredCovered q n e h he hl
  · exact g.noUseAfterFree

/-- A `load` keeps every fact: it happens only at the current epoch, which a published node's
birth does not exceed. -/
theorem load_good (s : St) (g : Good s) (r n : Nat) : Good (step s (.load r n)) := by
  by_cases hc : s.state n = .live ∧ s.res r = some s.now
  case neg => simp only [step, hc, ite_false]; exact g
  case pos =>
  simp only [step, hc, and_self, ite_true]
  constructor
  · exact g.liveBorn
  · -- The loader's reservation is the epoch; the others are as they were.
    intro q m h
    by_cases hq : q = r
    · exact ⟨s.now, hq ▸ hc.2, Nat.le_refl _⟩
    · simp [hq] at h; exact g.holderPinned q m h
  · -- The loaded node's birth is at most the epoch, the loader's reservation.
    intro q m e h he hl
    by_cases hq : q = r
    · simp [hq] at h; subst h
      rw [hq, hc.2] at he; injection he with he; subst he
      exact g.liveBorn n hl
    · simp [hq] at h; exact g.liveCovered q m e h he hl
  · -- The loaded node is published, not retired.
    intro q m e h he hl
    by_cases hq : q = r
    · simp [hq] at h; subst h; rw [hc.1] at hl; exact absurd hl (by decide)
    · simp [hq] at h; exact g.retiredCovered q m e h he hl
  · -- The loaded node is published.
    intro q m h
    by_cases hq : q = r
    · simp [hq] at h; subst h; rw [hc.1]; decide
    · simp [hq] at h; exact g.noUseAfterFree q m h

/-- An `unpin` keeps every fact: the reader holds and reserves nothing afterwards. -/
theorem unpin_good (s : St) (g : Good s) (r : Nat) : Good (step s (.unpin r)) := by
  simp only [step]
  constructor
  · -- Births and the epoch are as they were.
    exact g.liveBorn
  · -- The reader holds nothing afterwards; every other reader is as it was.
    intro q n h
    by_cases hq : q = r
    · simp [hq] at h
    · simp [hq] at h ⊢; exact g.holderPinned q n h
  · -- The same for a held published node: only other readers hold one, unchanged.
    intro q n e h he hl
    by_cases hq : q = r
    · simp [hq] at h
    · simp [hq] at h he; exact g.liveCovered q n e h he hl
  · -- And for a held retired node.
    intro q n e h he hl
    by_cases hq : q = r
    · simp [hq] at h
    · simp [hq] at h he; exact g.retiredCovered q n e h he hl
  · -- No state changed, and the reader holds nothing: still no held pooled node.
    intro q n h
    by_cases hq : q = r
    · simp [hq] at h
    · simp [hq] at h; exact g.noUseAfterFree q n h

/-- A `retire` keeps every fact: each node it retires records the batch's smallest birth, which is
at most that node's own birth, which a reader holding it already had covered. -/
theorem retire_good (s : St) (g : Good s) (ns : List Nat) : Good (step s (.retire ns)) := by
  simp only [step]
  -- Name the published nodes the retire takes.
  generalize hl : ns.filter (fun m => s.state m = .live) = live
  cases live with
  | nil => exact g
  | cons head rest =>
    -- Every node the retire takes was published.
    have memLive : ∀ m, m ∈ head :: rest → s.state m = .live := by
      intro m hm
      rw [← hl] at hm
      simpa using (List.mem_filter.mp hm).2
    have headMem : head ∈ head :: rest := List.mem_cons_self
    -- The batch's smallest birth is at most each member's birth.
    have lowLe : ∀ m, m ∈ head :: rest →
        minOf ((head :: rest).map s.birth) ≤ s.birth m := fun m hm =>
      minOf_le _ _ (List.mem_map.mpr ⟨m, hm, rfl⟩)
    constructor
    · -- A node still published was not taken, so it is not the head either: birth unchanged.
      intro m h
      by_cases hm : m ∈ head :: rest
      · simp [hm] at h
      · have hh : m ≠ head := fun e => hm (e ▸ headMem)
        simp [hm, hh] at h ⊢; exact g.liveBorn m h
    · exact g.holderPinned
    · intro r m e h he hlv
      by_cases hm : m ∈ head :: rest
      · simp [hm] at hlv
      · have hh : m ≠ head := fun e => hm (e ▸ headMem)
        simp [hm, hh] at hlv ⊢; exact g.liveCovered r m e h he hlv
    · -- A node just retired: its batch's smallest birth is at most its birth, at most `e`.
      intro r m e h he hrt
      by_cases hm : m ∈ head :: rest
      · simp only [hm, ite_true]
        exact Nat.le_trans (lowLe m hm) (g.liveCovered r m e h he (memLive m hm))
      · simp [hm] at hrt ⊢; exact g.retiredCovered r m e h he hrt
    · intro r m h
      by_cases hm : m ∈ head :: rest
      · simp [hm]
      · simp [hm]; exact g.noUseAfterFree r m h

/-- A `free` keeps every fact, and in particular frees no node a reader holds: a reader holding a
retired node is covered by its batch, so it is not one the batch skips, and the free waits for
every covering reader. -/
theorem free_good (s : St) (g : Good s) (n : Nat) : Good (step s (.free n)) := by
  by_cases hc : MayFree s n
  case neg => simp only [step, hc, ite_false]; exact g
  case pos =>
  simp only [step, hc, ite_true]
  -- No reader holds `n`: a holder would be both covered and skipped by the batch.
  have nobody : ∀ r, s.holds r ≠ some n := by
    intro r h
    obtain ⟨e, he, hlt⟩ := hc.2 r h
    have hcov := g.retiredCovered r n e h he hc.1
    omega
  constructor
  · intro m h
    by_cases hm : m = n
    · simp [hm] at h
    · simp [hm] at h; exact g.liveBorn m h
  · exact g.holderPinned
  · intro r m e h he hlv
    by_cases hm : m = n
    · exact absurd (hm ▸ h) (nobody r)
    · simp [hm] at hlv; exact g.liveCovered r m e h he hlv
  · intro r m e h he hrt
    by_cases hm : m = n
    · exact absurd (hm ▸ h) (nobody r)
    · simp [hm] at hrt; exact g.retiredCovered r m e h he hrt
  · intro r m h
    by_cases hm : m = n
    · exact absurd (hm ▸ h) (nobody r)
    · simp [hm]; exact g.noUseAfterFree r m h

/-- Every operation but the mutation keeps every fact. -/
theorem step_good (s : St) (g : Good s) (op : Op) (fresh : op.Fresh) : Good (step s op) := by
  cases op with
  | tick => exact tick_good s g
  | take n b => exact take_good s g n b
  | takeStale n junk => exact absurd fresh id
  | pin r => exact pin_good s g r
  | raise r => exact raise_good s g r
  | load r n => exact load_good s g r n
  | unpin r => exact unpin_good s g r
  | retire ns => exact retire_good s g ns
  | free n => exact free_good s g n

/-- Every run of operations without the mutation keeps every fact. -/
theorem run_good (s : St) (g : Good s) (ops : List Op) (fresh : ∀ op ∈ ops, op.Fresh) :
    Good (run s ops) := by
  -- By induction on the operations: each step keeps the facts (`step_good`).
  induction ops generalizing s with
  | nil => exact g
  | cons op ops ih =>
    exact ih (step s op) (step_good s g op (fresh op List.mem_cons_self))
      (fun o ho => fresh o (List.mem_cons_of_mem op ho))

/-! ## What the stamp buys -/

/-- With every recycled node re-initialised before it is published again, no reader ever holds a
node that is back in the pool, whatever the run: no use after free. -/
theorem no_use_after_free (ops : List Op) (hops : ∀ op ∈ ops, op.Fresh) (r n : Nat)
    (h : (run fresh ops).holds r = some n) : (run fresh ops).state n ≠ .pooled :=
  -- The facts hold from the start (`fresh_good`) through every fresh step (`run_good`).
  (run_good fresh fresh_good ops hops).noUseAfterFree r n h

/-- And no batch ever skips a reader that holds one of its nodes: the reservation of every reader
holding a retired node is at least its batch's smallest birth. -/
theorem batch_covers_its_holders (ops : List Op) (hops : ∀ op ∈ ops, op.Fresh) (r n e : Nat)
    (h : (run fresh ops).holds r = some n) (he : (run fresh ops).res r = some e)
    (hrt : (run fresh ops).state n = .retired) :
    ¬ Skipped (run fresh ops) r ((run fresh ops).batchMin n) := by
  -- Being skipped means a reservation below the smallest birth; `retiredCovered` says it is not.
  intro ⟨e', he', hlt⟩
  rw [he] at he'
  injection he' with he'
  subst he'
  have hcov := (run_good fresh fresh_good ops hops).retiredCovered r n e h he hrt
  omega

/-! ## What skipping the stamp breaks -/

/-- The run of the mutation, step by step: node 0 taken without the fresh header and born at 5
(what the pool wrote), reader 1 pinned at epoch 0 loads it, the node is retired (its batch's
smallest birth is 5), and the free runs, since the only reader holding it has a reservation, 0,
below 5. -/
noncomputable def staleRun : List Op := [.takeStale 0 5, .pin 1, .load 1 0, .retire [0], .free 0]

/-- The state just before the free: node 0 retired with smallest birth 5, held by reader 1 whose
reservation is 0, and held by nobody else. -/
theorem before_free :
    let s := run fresh [.takeStale 0 5, .pin 1, .load 1 0, .retire [0]]
    s.state 0 = .retired ∧ s.batchMin 0 = 5 ∧ s.holds 1 = some 0 ∧ s.res 1 = some 0 ∧
      ∀ r, r ≠ 1 → s.holds r = none := by
  -- Each operation's condition holds at its turn, so the state can be computed outright.
  simp [run, step, fresh, minOf]

/-- Skipping the fresh header breaks the protection: after the mutation's run, reader 1 still holds
node 0, and node 0 is back in the pool. This is the sequential shape of the reclamation model's
`RC_mut_stale_link_birth` counterexample. -/
theorem stale_take_frees_a_held_node :
    (run fresh staleRun).holds 1 = some 0 ∧ (run fresh staleRun).state 0 = .pooled := by
  obtain ⟨hst, hmin, hh, hres, hother⟩ := before_free
  -- The free's condition holds: the only holder is reader 1, skipped (0 < 5).
  have hmay : MayFree (run fresh [.takeStale 0 5, .pin 1, .load 1 0, .retire [0]]) 0 := by
    refine ⟨hst, fun r hr => ?_⟩
    by_cases h1 : r = 1
    · subst h1; exact ⟨0, hres, by omega⟩
    · rw [hother r h1] at hr; exact absurd hr (by simp)
  have hsplit : run fresh staleRun =
      step (run fresh [.takeStale 0 5, .pin 1, .load 1 0, .retire [0]]) (.free 0) := by
    simp [staleRun, run]
  rw [hsplit]
  simp only [step, hmay, ite_true]
  exact ⟨hh, by simp⟩

/-- So the mutation is the only way out: the counterexample's run is not a run of fresh
operations, since it starts with a take that skips the header. -/
theorem staleRun_not_fresh : ¬ ∀ op ∈ staleRun, op.Fresh := by
  intro h
  exact h (.takeStale 0 5) (by simp [staleRun])

end Kovan.Recycle
