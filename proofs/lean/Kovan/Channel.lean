/-!
# The channels' counters and the waker's state word

This file checks the arithmetic `kovan-channel` (`kovan-channel/src`) rests on. The TLA+ model in
`proofs/tla/channel` checks how threads interleave on the channels, with a capacity of one and a
few threads; here the code's own constants and counters are taken as they are: the
`AtomicWaker` state word of a 64-bit `usize` (`signal.rs`), the bounded channel's `len` against
any capacity (`flavors/bounded.rs`), the sender count of either flavor and the bounded
flavor's receiver count, and the three states of a signal (`signal.rs`).

The code has no ring, no lap and no wrapping stamp: the bounded flavor is the unbounded flavor's
linked list with a count of the slots in use, and that list has pointers, no indices. These three
and the signal's state word are all the arithmetic there is.

## The story in plain words

1. An `AsyncSignal`'s waker sits in one cell guarded by a word with two bits: `WAITING = 0`,
   `REGISTERING = 1`, `WAKING = 2`. `take`'s `fetch_or(WAKING)` sets the high bit and keeps the
   low one, and its `fetch_and(!WAKING)` clears the high bit and keeps the low one; on the four
   words the state can hold they are what the TLA+ model writes (`IF p >= 2 THEN p ELSE p + 2`,
   `IF p >= 2 THEN p - 2 ELSE p`), and both keep the word among those four.
2. One `register` and one `take` (the start of a `wake`), interleaved in every way: they never
   hold the cell at once, the waker being registered is never lost (it is woken, or it stays in
   the cell for the next wake), and when the take's `fetch_or` comes after the register's first
   compare-and-swap, that waker is woken, by the take or by the register itself. A take that
   comes first wakes the waker registered before, if any: a waiter re-checks its condition after
   it registers, so that wake is not one it needs.
3. A bounded send reserves a slot with `len.compare_exchange(len, len + 1)` only when `len` was
   below the capacity and links its message only after that; a receive takes a message out of
   the list and only then gives a slot back with `len.fetch_sub(1)`. However the threads
   interleave, the messages in the list never exceed `len`, `len` never exceeds the capacity, the
   reserve's `len + 1` never overflows a `usize`, and `fetch_sub` never takes `len` below zero.
4. The sender count starts at one, a clone adds one while a handle lives, a drop takes one. The
   drop that sees one is the last event the count has: exactly one drop stores the disconnected
   flag, and no clone or drop follows it. The bounded flavor's receiver count is the same counter
   on the `Receiver` handles, and its last drop stores `receivers_gone` the same way.
5. A signal is `WAITING = 0`, `NOTIFIED = 1` (a notifier woke it) or `CANCELLED = 2` (its owner
   withdrew it). A notifier's `try_notify` and the owner's `cancel` are each a compare-and-swap
   from `WAITING`: of all the operations a signal meets, the first wins and every later one
   loses. A wakeup goes to one notifier's waiter or back to its owner, never both and never
   twice, and the owner whose cancel lost knows a notifier woke it and passes the wakeup on.

## What the model leaves out

Which thread wins a compare-and-swap, the wait lists, the signals and the list are the TLA+
model's business; the interleavings of item 2 are of one register and one take. Nothing here is
about memory ordering. Item 5 is the arithmetic of the word; which operation comes first, and
what the waiters do with the answer, is the model's (`CH_mut_check_then_notify` puts back the rule
before the fix, a check and then a store, and loses a wakeup). The count of item 4 is bounded by the handles alive, which `Arc` keeps
below `isize::MAX`, so it never wraps a `usize`.
-/

namespace Kovan.Channel

/-! ## The AtomicWaker word -/

/-- `WAITING`: no registration or wake in flight. -/
def waiting : Nat := 0

/-- `REGISTERING`: `register` holds the cell. -/
def registering : Nat := 1

/-- `WAKING`: `take` holds (or has claimed) the cell. -/
def waking : Nat := 2

/-- `!WAKING` of a 64-bit `usize`. -/
def notWaking : Nat := 2 ^ 64 - 1 - waking

/-- `state.fetch_or(WAKING)`: the word it leaves. -/
def fetchOr (w : Nat) : Nat := w ||| waking

/-- `state.fetch_and(!WAKING)`: the word it leaves. -/
def fetchAnd (w : Nat) : Nat := w &&& notWaking

/-- The or of `WAKING` is the model's `IF p >= 2 THEN p ELSE p + 2` on every value of the word. -/
theorem fetchOr_model : ∀ p, p < 4 → fetchOr p = if 2 ≤ p then p else p + 2 := by decide

/-- The and of `!WAKING` is the model's `IF p >= 2 THEN p - 2 ELSE p` on every value of the
word. -/
theorem fetchAnd_model : ∀ p, p < 4 → fetchAnd p = if 2 ≤ p then p - 2 else p := by decide

/-- Both keep the word two bits: the state never leaves its four values. -/
theorem word_closed : ∀ p, p < 4 → fetchOr p < 4 ∧ fetchAnd p < 4 := by decide

/-- `fetch_or` sets `WAKING` and keeps `REGISTERING`; `fetch_and` clears `WAKING` and keeps
`REGISTERING`. -/
theorem bits : ∀ p, p < 4 →
    fetchOr p &&& waking = waking ∧ fetchOr p &&& registering = p &&& registering ∧
    fetchAnd p &&& waking = 0 ∧ fetchAnd p &&& registering = p &&& registering := by decide

/-- A take's or into a registration in flight leaves `REGISTERING | WAKING`, the one value the
register's hand-back compare-and-swap can fail on, the value its `debug_assert_eq!` names. -/
theorem raced : fetchOr registering = registering ||| waking ∧ registering ||| waking = 3 := by
  decide

/-- A take that set `WAKING` from `WAITING` and hands the cell back leaves `WAITING`. -/
theorem take_round_trip : fetchAnd (fetchOr waiting) = waiting := by decide

/-! ## One register against one take

The steps of `AtomicWaker::register` (signal.rs:283-342) and of `take` with the wake after it
(signal.rs:345-371), each step one atomic operation or one access to the cell. The cell holds no
waker, the one registered before (`old`), or the one being registered (`new`). -/

/-- What the cell holds. -/
inductive Cell where
  | none
  | old
  | new
  deriving DecidableEq, Repr

/-- The two operations' state: the word, the cell, where each is (`pcR = 7`, `pcT = 5`: done),
what each took out of the cell, which wakers were woken, and whether the take's `fetch_or` came
after the register's first compare-and-swap. -/
structure St where
  word : Nat
  cell : Cell
  pcR : Nat
  pcT : Nat
  heldR : Cell
  heldT : Cell
  wokeNew : Bool
  wokeOld : Bool
  takeAfter : Bool
  deriving DecidableEq, Repr

/-- A waker woken. -/
def wake (s : St) : Cell → St
  | .new => { s with wokeNew := true }
  | .old => { s with wokeOld := true }
  | .none => s

/-- One step of `register`. -/
def stepR (s : St) : St :=
  match s.pcR with
  | 1 =>
    -- compare_exchange(WAITING, REGISTERING); WAKING: wake_by_ref; else another register
    if s.word = waiting then { s with word := registering, pcR := 2 }
    else if s.word = waking then { wake s .new with pcR := 7 }
    else { s with pcR := 7 }
  | 2 => { s with cell := .new, pcR := 3 }  -- *waker = Some(waker.clone())
  | 3 =>
    -- compare_exchange(REGISTERING, WAITING); its failure: a wake raced the registration
    if s.word = registering then { s with word := waiting, pcR := 7 } else { s with pcR := 4 }
  | 4 => { s with heldR := s.cell, cell := .none, pcR := 5 }  -- take().unwrap()
  | 5 => { s with word := waiting, pcR := 6 }  -- swap(WAITING)
  | 6 => { wake s s.heldR with pcR := 7 }  -- waker.wake()
  | _ => s

/-- One step of `take`, then the wake of what it took. -/
def stepT (s : St) : St :=
  match s.pcT with
  | 1 =>
    -- fetch_or(WAKING): the cell is the take's only when the word was WAITING
    let s' := { s with word := fetchOr s.word, takeAfter := decide (2 ≤ s.pcR) }
    if s.word = waiting then { s' with pcT := 2 } else { s' with pcT := 5 }
  | 2 => { s with heldT := s.cell, cell := .none, pcT := 3 }  -- (*waker).take()
  | 3 => { s with word := fetchAnd s.word, pcT := 4 }  -- fetch_and(!WAKING)
  | 4 => { wake s s.heldT with pcT := 5 }  -- waker.wake()
  | _ => s

/-- Each holds the cell between the step that claims it and the step that hands it back. -/
def exclusive (s : St) : Bool := !(decide (2 ≤ s.pcR ∧ s.pcR ≤ 5) && decide (2 ≤ s.pcT ∧ s.pcT ≤ 3))

/-- When both are done: the new waker was woken or still sits in the cell, and woken if the take
came after the register began; the word is back to `WAITING`. -/
def ends (s : St) : Bool :=
  !(decide (s.pcR = 7 ∧ s.pcT = 5)) ||
    ((s.wokeNew || decide (s.cell = .new)) && (!s.takeAfter || s.wokeNew) &&
      decide (s.word = waiting))

/-- A schedule: `true` steps the register, `false` the take (a done one stands still). The
check holds at every state on the way. -/
def runOk : St → List Bool → Bool
  | s, [] => exclusive s && ends s
  | s, b :: l => exclusive s && runOk (if b then stepR s else stepT s) l

/-- Every schedule of `n` steps. -/
def schedules : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (schedules n).flatMap fun l => [true :: l, false :: l]

def start (c : Cell) : St :=
  { word := waiting, cell := c, pcR := 1, pcT := 1, heldR := .none, heldT := .none,
    wokeNew := false, wokeOld := false, takeAfter := false }

set_option maxRecDepth 100000 in
/-- The register takes at most six steps and the take four: ten steps cover every
interleaving of the two, and every one is checked, with a waker registered before and without. -/
theorem register_against_take :
    (schedules 10).all (runOk (start .old)) = true ∧
    (schedules 10).all (runOk (start .none)) = true := by decide

/-! ## The bounded channel's slots

The counts of the events on one bounded channel: slots reserved (the successful compare-and-swap
of `len`), messages linked into the list, messages taken out of it, slots given back (the
`fetch_sub`). `len` is the slots reserved less those given back. -/

structure Counts where
  reserved : Nat
  sent : Nat
  taken : Nat
  released : Nat

/-- The events, each allowed as the code orders them: a reserve only when `len` is below the
capacity (the compare-and-swap succeeds only on the `len` it checked); a send's link only after
its reserve; a take only of a message linked; a release only after its take. -/
inductive Step (cap : Nat) : Counts → Counts → Prop where
  | reserve {c : Counts} : c.reserved - c.released < cap →
      Step cap c { c with reserved := c.reserved + 1 }
  | send {c : Counts} : c.sent < c.reserved → Step cap c { c with sent := c.sent + 1 }
  | take {c : Counts} : c.taken < c.sent → Step cap c { c with taken := c.taken + 1 }
  | release {c : Counts} : c.released < c.taken → Step cap c { c with released := c.released + 1 }

/-- The counts of a channel some interleaving of its threads reaches. -/
inductive Reach (cap : Nat) : Counts → Prop where
  | init : Reach cap ⟨0, 0, 0, 0⟩
  | step {c d : Counts} : Reach cap c → Step cap c d → Reach cap d

/-- Every reachable count keeps each event behind the one it follows, and the slots in use within
the capacity. -/
def Inv (cap : Nat) (c : Counts) : Prop :=
  c.released ≤ c.taken ∧ c.taken ≤ c.sent ∧ c.sent ≤ c.reserved ∧ c.reserved ≤ c.released + cap

theorem reach_inv {cap : Nat} {c : Counts} (h : Reach cap c) : Inv cap c := by
  induction h with
  | init => simp [Inv]
  | step _ hs ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    cases hs <;> simp only [Inv] <;> omega

/-- Capacity: the messages in the list never exceed `len`, nor `len` the capacity. -/
theorem capacity {cap : Nat} {c : Counts} (h : Reach cap c) :
    c.sent - c.taken ≤ c.reserved - c.released ∧ c.reserved - c.released ≤ cap := by
  obtain ⟨h1, h2, h3, h4⟩ := reach_inv h
  omega

/-- The reserve's `len + 1` is at most the capacity, so it never overflows a `usize`. -/
theorem reserve_fits {cap : Nat} {c : Counts} (hcap : cap ≤ 2 ^ 64 - 1)
    (hr : c.reserved - c.released < cap) : c.reserved - c.released + 1 < 2 ^ 64 := by
  omega

/-- A release finds `len` at least one: `fetch_sub(1)` never wraps. -/
theorem release_positive {cap : Nat} {c : Counts} (h : Reach cap c)
    (hr : c.released < c.taken) : 1 ≤ c.reserved - c.released := by
  obtain ⟨h1, h2, h3, h4⟩ := reach_inv h
  omega

/-! ## The sender count -/

/-- `Sender::clone` and `Sender`'s drop: the count before, the count after. Both need a live
handle, so a count of at least one. -/
inductive Handle where
  | clone
  | drop
  deriving DecidableEq

def handleStep : Nat → Handle → Option Nat
  | n, .clone => if 1 ≤ n then some (n + 1) else none
  | n, .drop => if 1 ≤ n then some (n - 1) else none

/-- The count after a run of events from `n`, if every event had a live handle. -/
def run : Nat → List Handle → Option Nat
  | n, [] => some n
  | n, e :: l => (handleStep n e).bind fun m => run m l

/-- The drops of a run from `n` that see one (`fetch_sub(1) == 1`): those that disconnect. -/
def lastDrops : Nat → List Handle → Nat
  | _, [] => 0
  | n, e :: l =>
    match handleStep n e with
    | none => 0
    | some m => (if e = .drop ∧ n = 1 then 1 else 0) + lastDrops m l

/-- No event follows a count of zero. -/
theorem run_from_zero (l : List Handle) (h : l ≠ []) : run 0 l = none := by
  cases l with
  | nil => exact absurd rfl h
  | cons e l => cases e <;> rfl

/-- A run from a positive count that stays positive has no disconnecting drop; one that ends at
zero has exactly one, and it is the run's last event. -/
theorem one_disconnect :
    ∀ (l : List Handle) (n m : Nat), 1 ≤ n → run n l = some m →
      (1 ≤ m → lastDrops n l = 0) ∧
      (m = 0 → lastDrops n l = 1 ∧ ∃ l', l = l' ++ [.drop]) := by
  intro l
  induction l with
  | nil =>
    intro n m hn h
    simp only [run, Option.some.injEq] at h
    subst h
    exact ⟨fun _ => rfl, fun h0 => absurd h0 (by omega)⟩
  | cons e l ih =>
    intro n m hn h
    cases e with
    | clone =>
      have hs : handleStep n .clone = some (n + 1) := by simp [handleStep, hn]
      simp only [run, hs, Option.bind_some] at h
      have := ih (n + 1) m (by omega) h
      simp only [lastDrops, hs, reduceCtorEq, false_and, ↓reduceIte, Nat.zero_add]
      refine ⟨this.1, fun h0 => ⟨(this.2 h0).1, ?_⟩⟩
      obtain ⟨l', hl'⟩ := (this.2 h0).2
      exact ⟨.clone :: l', by simp [hl']⟩
    | drop =>
      have hs : handleStep n .drop = some (n - 1) := by simp [handleStep, hn]
      simp only [run, hs, Option.bind_some] at h
      by_cases h1 : n = 1
      · subst h1
        cases l with
        | nil =>
          simp only [run, Option.some.injEq] at h
          subst h
          exact ⟨fun h0 => absurd h0 (by omega), fun _ => ⟨rfl, [], rfl⟩⟩
        | cons e l => simp [run_from_zero (e :: l) (by simp)] at h
      · have := ih (n - 1) m (by omega) h
        simp only [lastDrops, hs, h1, and_false, ↓reduceIte, Nat.zero_add]
        refine ⟨this.1, fun h0 => ⟨(this.2 h0).1, ?_⟩⟩
        obtain ⟨l', hl'⟩ := (this.2 h0).2
        exact ⟨.drop :: l', by simp [hl']⟩

/-- From the one handle `channel()` returns: every run that drops every handle has exactly one
drop that disconnects, its last event. -/
theorem disconnect_once (l : List Handle) (h : run 1 l = some 0) :
    lastDrops 1 l = 1 ∧ ∃ l', l = l' ++ [.drop] :=
  (one_disconnect l 1 0 (Nat.le_refl 1) h).2 rfl

/-! ## The signal's state word -/

/-- `NOTIFIED`: a notifier woke the signal. -/
def notified : Nat := 1

/-- `CANCELLED`: the signal's owner withdrew it. -/
def cancelled : Nat := 2

/-- A notifier's `try_notify` or the owner's `cancel`: each a compare-and-swap from `WAITING`. -/
inductive SigOp where
  | tryNotify
  | cancel
  deriving DecidableEq

/-- The word an operation leaves, and whether its compare-and-swap won. -/
def sigStep (w : Nat) : SigOp → Nat × Bool
  | .tryNotify => if w = waiting then (notified, true) else (w, false)
  | .cancel => if w = waiting then (cancelled, true) else (w, false)

/-- The operations of a run from the word `w` that won. -/
def wins : Nat → List SigOp → Nat
  | _, [] => 0
  | w, o :: l => (if (sigStep w o).2 then 1 else 0) + wins (sigStep w o).1 l

/-- Once the word has left `WAITING`, no operation wins. -/
theorem wins_from_set (w : Nat) (hw : w ≠ waiting) : ∀ l, wins w l = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons o l ih => cases o <;> simp [wins, sigStep, hw, ih]

/-- From a fresh signal the first operation wins and every later one loses: one notifier's
wakeup, or the owner's withdrawal, never both and never two. -/
theorem one_winner (o : SigOp) (l : List SigOp) : wins waiting (o :: l) = 1 := by
  have hn : notified ≠ waiting := by decide
  have hc : cancelled ≠ waiting := by decide
  cases o
  · simp [wins, sigStep, wins_from_set notified hn l]
  · simp [wins, sigStep, wins_from_set cancelled hc l]

/-- An owner's cancel that lost found the signal notified, unless it was withdrawn already: the
wakeup is the owner's to pass on. -/
theorem cancel_lost (w : Nat) (hw : w ≤ cancelled) (h : (sigStep w .cancel).2 = false) :
    w = notified ∨ w = cancelled := by
  simp only [sigStep] at h
  split at h
  · exact absurd h (by decide)
  · simp only [notified, cancelled, waiting] at *
    omega

end Kovan.Channel
