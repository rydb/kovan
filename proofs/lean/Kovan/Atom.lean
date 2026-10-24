import Kovan.Magazine

/-!
# The atomic shared value's nodes, identity test and birth epochs

This file checks the arithmetic `Atom` and `AtomOption` (`kovan/src/atom.rs`) rest on. The TLA+
model in `proofs/tla/atom` checks how threads interleave on them, with kovan's reclamation reduced
to the rule the comparisons below make; here the code's own layout, comparisons and constants are
taken as they are, on a 64-bit target. `atom.rs` packs no words and tags no pointers: what it
computes is where the value sits in a node, which two pointers `compare_and_swap` compares, and
which readers a retired node's birth epoch makes the node wait for.

## The story in plain words

1. A node is `#[repr(C)]`: the 40-byte `RetiredNode` header first, at offset 0, so the casts to
   `*mut RetiredNode` read the header, then the value at the header's size rounded up to the
   value's alignment. A `Removed` holds the node itself, so a value swapped out keeps that layout
   until the node is retired. A `u64` node is 48 bytes (the 48-byte class), a `String` node 64.
2. `compare_and_swap` compares the value pointer of the node it loads with `current`'s value
   pointer, each the node's address plus the same offset. Adding the offset, even modulo `2^64`,
   sends different addresses to different pointers, so the compare is a compare of the nodes.
3. `try_retire` skips a slot whose published epoch is below the batch's birth epoch, which
   `enqueue_node` keeps at the least birth of the batch's nodes. So a slot that publishes an epoch
   at or past the birth of any one node of the batch is never skipped for it, and the
   unconditional reservation (`u64::MAX`) is skipped for no batch.
4. A thread's cached birth epoch is the global epoch it last read; the global epoch only grows, so
   the cache is never above it. A node is stamped with the cache when it is allocated, before it
   is published; a reader that loads it reads the global epoch after the pointer and its slot then
   publishes at least that. So the reader's slot is not skipped for the node's batch.
   `Removed::drop` retires the node itself, which keeps its own birth, so the node's batch is
   placed in every such reader's slot and the value waits for them. A fresh stamp instead (the
   rule before 6b1cb09, when the value was retired in a wrapper of its own) is skipped by a reader
   whose epoch the global one has moved past: a reader at epoch 1, a stamp of 2.
5. The guard `compare_and_swap` returns on success holds a node it never loaded. The node was
   allocated before the protected load, so its birth is at most the global epoch then, and the
   load leaves the slot publishing at least the epoch it read after: the slot is not skipped for
   that node's batch either. Without the load's raise, a section whose own retire advanced the
   epoch (and its cached birth with it) can publish less than the node's birth: skipped.

## What the model leaves out

Addresses, epochs and sizes are natural numbers; the comparisons are the code's. The layout is
`#[repr(C)]`'s rule for a struct of two fields on a 64-bit target, where `RetiredNode` is five
8-byte fields aligned to 8 (on a 32-bit target its pointer fields are 4 bytes, and the class of a
node changes accordingly). Which slot is live, active or in a transition when a batch is scanned,
and when a batch is submitted, is the reclamation's business (`proofs/tla/reclaim`); nothing here
is about threads or memory ordering.
-/

namespace Kovan.Atom

open Kovan.Magazine (classOf classAlign)

/-! ## The node's layout -/

/-- A type's size and alignment, in bytes. -/
structure Layout where
  size : Nat
  align : Nat
  deriving DecidableEq, Repr

/-- The least multiple of `a` at or past `n`, for `a > 0`. -/
def alignUp (n a : Nat) : Nat := (n + a - 1) / a * a

/-- `RetiredNode`: `#[repr(C, align(8))]`, its five fields (`next`, `batch_link`, `refs_or_next`,
`birth_epoch`, `destructor`) 8 bytes each on a 64-bit target. -/
def retiredNode : Layout := ⟨5 * 8, 8⟩

/-- The offset of the second field of a `#[repr(C)]` struct: the first's size rounded up to the
second's alignment. -/
def secondOffset (h t : Layout) : Nat := alignUp h.size t.align

/-- A `#[repr(C)]` struct of two fields: the second at `secondOffset`, the whole rounded up to the
larger alignment. -/
def reprC2 (h t : Layout) : Layout :=
  ⟨alignUp (secondOffset h t + t.size) (max h.align t.align), max h.align t.align⟩

/-- `AtomNode<T>`: `{ _retired: RetiredNode, val: T }`. -/
def atomNode (t : Layout) : Layout := reprC2 retiredNode t

/-- `AtomNode::val_ptr`'s offset, `addr_of!((*ptr).val)` from the node's address. -/
def valOffset (t : Layout) : Nat := secondOffset retiredNode t

theorem alignUp_ge (n : Nat) {a : Nat} (ha : 0 < a) : n ≤ alignUp n a := by
  unfold alignUp
  have h := Nat.div_add_mod (n + a - 1) a
  have hm := Nat.mod_lt (n + a - 1) ha
  rw [Nat.mul_comm] at h
  generalize (n + a - 1) / a * a = m at h ⊢
  generalize (n + a - 1) % a = r at h hm
  omega

theorem alignUp_dvd (n a : Nat) : a ∣ alignUp n a := ⟨(n + a - 1) / a, Nat.mul_comm _ _⟩

/-- The header comes first, at offset 0, and the value starts past its last byte, at a multiple
of the value's alignment: the header and the value never overlap, and the value is aligned. -/
theorem value_after_header (t : Layout) (ha : 0 < t.align) :
    retiredNode.size ≤ valOffset t ∧ t.align ∣ valOffset t :=
  ⟨alignUp_ge _ ha, alignUp_dvd _ _⟩

/-- The node holds the whole value. -/
theorem node_holds_value (t : Layout) (ha : 0 < max retiredNode.align t.align) :
    valOffset t + t.size ≤ (atomNode t).size :=
  alignUp_ge _ ha

/-- For a value aligned to at most 8 the value sits right after the 40-byte header; aligned to 16
it starts at 48. -/
theorem valOffset_eq (t : Layout) :
    (t.align ∈ [1, 2, 4, 8] → valOffset t = 40) ∧ (t.align = 16 → valOffset t = 48) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;>
      simp [valOffset, secondOffset, alignUp, retiredNode, h]
  · simp [valOffset, secondOffset, alignUp, retiredNode, h]

/-- `u64`, `String`, `u128`, and a 985-byte array: 48 bytes (the 48-byte class), 64 (the 64-byte
class), 64 aligned to 16 (the 64-byte class), and 1032, past the largest class (a `Box`). -/
example : atomNode ⟨8, 8⟩ = ⟨48, 8⟩ ∧ classOf 48 8 = some 2 := by decide
example : atomNode ⟨24, 8⟩ = ⟨64, 8⟩ ∧ classOf 64 8 = some 3 := by decide
example : atomNode ⟨16, 16⟩ = ⟨64, 16⟩ ∧ classOf 64 16 = some 3 := by decide
example : atomNode ⟨985, 1⟩ = ⟨1032, 8⟩ ∧ classOf 1032 8 = none := by decide

/-- Every node of a value aligned to at most 8 (a Rust alignment is a power of two) and of at most
984 bytes takes a class: the node is at most 1 KiB. -/
theorem node_takes_a_class {t : Layout} (ha : t.align ∈ [1, 2, 4, 8]) (hs : t.size ≤ 984) :
    (classOf (atomNode t).size (atomNode t).align).isSome := by
  have hoff : valOffset t = 40 := (valOffset_eq t).1 ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  have hal : max retiredNode.align t.align = 8 := Nat.max_eq_left (by simp only [retiredNode]; omega)
  have hsize : (atomNode t).size = alignUp (40 + t.size) 8 := by
    show alignUp (secondOffset retiredNode t + t.size) (max retiredNode.align t.align) = _
    rw [hal, show secondOffset retiredNode t = valOffset t from rfl, hoff]
  have halign : (atomNode t).align = 8 := hal
  have h0 : 0 < (atomNode t).size := by rw [hsize]; simp only [alignUp]; omega
  have h1 : (atomNode t).size ≤ 1024 := by rw [hsize]; simp only [alignUp]; omega
  have h2 : (atomNode t).align ≤ classAlign := by rw [halign]; decide
  obtain ⟨i, hi, -⟩ := Kovan.Magazine.classOf_fits h0 h1 h2
  rw [hi]
  rfl

/-! ## The identity test of `compare_and_swap` -/

/-- A value pointer: the node's address plus the value's offset, as a `usize`. -/
def valPtr (node off : Nat) : Nat := (node + off) % 2 ^ 64

/-- Two value pointers at one offset are equal exactly when the nodes' addresses are: the
`current_val_ptr != current.ptr` test of `compare_and_swap` compares nodes. -/
theorem valPtr_eq_iff {p q : Nat} (off : Nat) (hp : p < 2 ^ 64) (hq : q < 2 ^ 64) :
    valPtr p off = valPtr q off ↔ p = q := by
  constructor
  · intro h
    simp only [valPtr, Nat.reducePow] at h hp hq
    omega
  · intro h
    rw [h]

/-! ## Birth epochs -/

/-- `try_retire`'s scan: a slot publishing `epoch` is skipped for a batch whose birth is
`minEpoch` when `epoch < min_epoch`. -/
def skipped (epoch minEpoch : Nat) : Bool := decide (epoch < minEpoch)

/-- `enqueue_node`'s update of the batch's birth (kept on its refs-node): lowered to the new
node's birth when that is lower. -/
def lowerBirth (refs birth : Nat) : Nat := if refs > birth then birth else refs

/-- The birth of a batch: its first node is the refs-node, and every later node lowers the
refs-node's birth to its own when its own is lower. (A batch is never empty.) -/
def batchBirth : List Nat → Nat
  | [] => 0
  | b :: bs => bs.foldl lowerBirth b

theorem lowerBirth_eq_min (r b : Nat) : lowerBirth r b = min r b := by
  unfold lowerBirth
  split <;> omega

theorem foldl_lower_le_init (bs : List Nat) (b : Nat) : bs.foldl lowerBirth b ≤ b := by
  induction bs generalizing b with
  | nil => exact Nat.le_refl b
  | cons c cs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (ih _) (by rw [lowerBirth_eq_min]; exact Nat.min_le_left b c)

theorem foldl_lower_le_mem {bs : List Nat} {x : Nat} (hx : x ∈ bs) (b : Nat) :
    bs.foldl lowerBirth b ≤ x := by
  induction bs generalizing b with
  | nil => simp at hx
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with h | h
    · subst h
      exact Nat.le_trans (foldl_lower_le_init _ _) (by rw [lowerBirth_eq_min]; exact Nat.min_le_right b x)
    · exact ih h _

/-- The batch's birth is at most the birth of each of its nodes. -/
theorem batchBirth_le {l : List Nat} {x : Nat} (hx : x ∈ l) : batchBirth l ≤ x := by
  cases l with
  | nil => simp at hx
  | cons b bs =>
    rcases List.mem_cons.mp hx with h | h
    · subst h; exact foldl_lower_le_init bs _
    · exact foldl_lower_le_mem h b

/-- A batch whose nodes are all born at or past `m` has a birth at or past `m`. -/
theorem foldl_lower_ge {bs : List Nat} {m b : Nat} (hb : m ≤ b) (h : ∀ x ∈ bs, m ≤ x) :
    m ≤ bs.foldl lowerBirth b := by
  induction bs generalizing b with
  | nil => exact hb
  | cons c cs ih =>
    simp only [List.foldl_cons]
    have hc := h c (List.mem_cons_self ..)
    apply ih
    · rw [lowerBirth_eq_min]; omega
    · exact fun x hx => h x (List.mem_cons_of_mem c hx)

/-- A slot that publishes an epoch at or past the birth of one node of a batch is not skipped for
the batch. -/
theorem not_skipped {l : List Nat} {x epoch : Nat} (hx : x ∈ l) (h : x ≤ epoch) :
    skipped epoch (batchBirth l) = false := by
  have := batchBirth_le hx
  simp only [skipped, decide_eq_false_iff_not, Nat.not_lt]
  omega

/-- `EPOCH_UNCONDITIONAL`, `u64::MAX`: the reservation a protected load escalates to. -/
def epochUnconditional : Nat := 2 ^ 64 - 1

/-- The unconditional reservation is skipped for no batch: every birth is a `u64`. -/
theorem unconditional_not_skipped {minEpoch : Nat} (h : minEpoch < 2 ^ 64) :
    skipped epochUnconditional minEpoch = false := by
  unfold skipped epochUnconditional
  simp only [Nat.reducePow, Nat.reduceSub] at h ⊢
  exact decide_eq_false (by omega)

/-- What changes a thread's cached birth epoch and the global epoch: an advance of the global
epoch (by any thread), and this thread caching the global epoch it reads (a transition at an
outermost pin, its own `increment_era` after advancing). -/
inductive Event
  | advance
  | cache

/-- The global epoch and the thread's cached birth epoch after one event. -/
def step : Nat × Nat → Event → Nat × Nat
  | (g, c), .advance => (g + 1, c)
  | (g, _), .cache => (g, g)

/-- The cached birth epoch never exceeds the global epoch: it starts at 0 (seeded from the global
epoch on first use, which is a `cache`), and the global epoch only grows. -/
theorem cached_le_global (evs : List Event) {g c : Nat} (h : c ≤ g) :
    (evs.foldl step (g, c)).2 ≤ (evs.foldl step (g, c)).1 := by
  induction evs generalizing g c with
  | nil => exact h
  | cons e es ih =>
    cases e with
    | advance => simp only [List.foldl_cons, step]; exact ih (by omega)
    | cache => simp only [List.foldl_cons, step]; exact ih (Nat.le_refl g)

/-- The global epoch never goes down. -/
theorem global_grows (evs : List Event) (g c : Nat) : g ≤ (evs.foldl step (g, c)).1 := by
  induction evs generalizing g c with
  | nil => exact Nat.le_refl g
  | cons e es ih =>
    cases e with
    | advance => simp only [List.foldl_cons, step]; exact Nat.le_trans (Nat.le_succ g) (ih _ _)
    | cache => simp only [List.foldl_cons, step]; exact ih _ _

/-- A reader's slot holds back a node it loaded. The node's birth is the allocating thread's cache,
at most the global epoch `e0` then; the node is published after, so the global epoch `e1` the
protected load reads after the pointer is at least `e0`, and the slot publishes at least `e1`. So
the slot is not skipped for any batch holding the node, which includes the node a `Removed`'s drop
retires. -/
theorem reader_not_skipped {birth e0 e1 published : Nat} {l : List Nat} (hb : birth ≤ e0)
    (he : e0 ≤ e1) (hp : e1 ≤ published) (hx : birth ∈ l) :
    skipped published (batchBirth l) = false :=
  not_skipped hx (by omega)

/-- The node `Removed::drop` retires keeps its own birth: in a batch of its own, or with others,
it is placed in every slot that holds back the node. -/
theorem removed_node_not_skipped {birth e0 e1 published : Nat} (others : List Nat) (hb : birth ≤ e0)
    (he : e0 ≤ e1) (hp : e1 ≤ published) :
    skipped published (batchBirth (birth :: others)) = false :=
  reader_not_skipped hb he hp (List.mem_cons_self ..)

/-- Why the node must keep its own birth: the rule before 6b1cb09 stamped the value's wrapper with
the dropping thread's cache, which an epoch advance after the reader's load had moved past the
reader's published epoch. The reader at 1 is skipped for a stamp of 2. -/
example : skipped 1 (batchBirth [2]) = true := by decide

/-- A fresh stamp above a reader's published epoch always skips it, when the stamped node is alone
in its batch or its batch holds nothing older. -/
theorem fresh_stamp_skipped {published fresh : Nat} (others : List Nat) (h : published < fresh)
    (hold : ∀ x ∈ others, fresh ≤ x) :
    skipped published (batchBirth (fresh :: others)) = true := by
  have hmin : fresh ≤ batchBirth (fresh :: others) := foldl_lower_ge (Nat.le_refl _) hold
  simp only [skipped, decide_eq_true_eq]
  omega

/-- The guard `compare_and_swap` returns on success: its node was allocated before the protected
load, with a birth at most the global epoch `e0` then, and the load leaves the section's slot
publishing at least the epoch `e1 ≥ e0` it read. The slot is not skipped for the node's batch. -/
theorem cas_guard_not_skipped {birth e0 e1 published : Nat} {l : List Nat} (hb : birth ≤ e0)
    (he : e0 ≤ e1) (hp : e1 ≤ published) (hx : birth ∈ l) :
    skipped published (batchBirth l) = false :=
  reader_not_skipped hb he hp hx

/-- Without the load's raise: a section published 1 when it pinned, its own retire's
`increment_era` moved the global epoch and its cache to 2, and the node it then allocated and
published is born at 2. The section is skipped for that node's batch. -/
example : ([Event.advance, Event.cache].foldl step (1, 1)) = (2, 2) ∧ skipped 1 (batchBirth [2]) = true := by
  decide

end Kovan.Atom
