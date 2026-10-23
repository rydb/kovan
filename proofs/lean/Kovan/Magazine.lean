/-!
# The magazine cache's classes, rings and bound

This file checks the arithmetic of kovan's magazine cache (`kovan/src/recycle.rs`, the `recycle`
feature). The TLA+ model in `proofs/tla/magazine` checks how threads interleave on it, with
tickets counted without wrapping and rings of two slots; here the code's own constants are taken
as they are: 20 classes up to 1 KiB, rings of 16 slots, tickets and turn words of 64 bits.

## The story in plain words

1. A node of `size` bytes takes the first class whose block size is at least `size`, so the
   smallest that fits; a node larger than 1 KiB, or aligned to more than 16 bytes, takes none. Every
   class size is a multiple of 16, so every block is aligned to 16.
2. Each ring's push and pop compare a slot's turn word with the turn of their ticket by the sign
   of their difference, both counted modulo `2^64`. While the two are fewer than `2^63` apart (they
   are never more than 16 apart), that sign is the sign of the difference of the true counts: the
   wrap of the counters never changes what a push or a pop decides. The turn of a wrapped ticket
   is the wrapped turn of the ticket.
3. A slot's word tells its three states apart for a ticket of its turn: waiting for this turn's
   push (equal to the turn), holding this turn's magazine (one more), handed to the next turn
   (the ring's size more), and the previous turn's magazine still waiting for its pop (one more
   than the previous turn). Each of the push's and the pop's three answers (take the slot, report
   the ring full or empty, reload the ticket) comes from exactly one of these.
4. The cache holds at most two magazines of 32 blocks per thread and class, and the depot 16 per
   class: for 64-byte nodes, 4 KiB per thread and 32 KiB in the depot.
5. A refill hands out the first block it takes from the slab layer and stores the others in the
   magazine so that the allocations after it pop them in the order they were taken. Carved from a
   chunk one after another they lie at rising addresses, so nodes allocated one after another
   do too, as with the global allocator, and a prefetcher streams them.

## What the model leaves out

The rings are their arithmetic: which thread wins a ticket is the TLA+ model's business. Nothing
here is about memory ordering.
-/

namespace Kovan.Magazine

/-! ## Size classes -/

/-- `CLASS_SIZES`: the block sizes of the classes, in bytes. -/
def classSizes : List Nat :=
  [16, 32, 48, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384, 448, 512, 640, 768, 896, 1024]

/-- `CLASS_ALIGN`: every block's alignment. -/
def classAlign : Nat := 16

/-- The loop of `class_of`: the index of the first size in the list that `size` fits. -/
def firstFit : List Nat → Nat → Option Nat
  | [], _ => none
  | c :: cs, size => if size ≤ c then some 0 else (firstFit cs size).map (· + 1)

/-- `class_of(size, align)`: no class for a zero-sized node or one aligned to more than 16. -/
def classOf (size align : Nat) : Option Nat :=
  if size = 0 ∨ classAlign < align then none else firstFit classSizes size

example : classOf 64 8 = some 3 := rfl
example : classOf 65 8 = some 4 := rfl
example : classOf 2000 8 = none := rfl

/-- `firstFit` answers an index whose size fits, every size before it being too small. -/
theorem firstFit_some {l : List Nat} {size i : Nat} (h : firstFit l size = some i) :
    ∃ hi : i < l.length, size ≤ l[i] ∧ ∀ j (hj : j < i), l[j]'(Nat.lt_trans hj hi) < size := by
  induction l generalizing i with
  | nil => simp [firstFit] at h
  | cons c cs ih =>
    unfold firstFit at h
    by_cases hc : size ≤ c
    · simp only [hc, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨by simp, by simpa using hc, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · simp only [hc, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨k, hk, rfl⟩ := h
      obtain ⟨hlt, hfit, hbefore⟩ := ih hk
      refine ⟨by simpa using hlt, by simpa using hfit, fun j hj => ?_⟩
      cases j with
      | zero => simpa using Nat.lt_of_not_le hc
      | succ j => simpa using hbefore j (by omega)

/-- `firstFit` answers some index whenever a size of the list fits. -/
theorem firstFit_isSome {l : List Nat} {size : Nat} (h : ∃ c ∈ l, size ≤ c) :
    (firstFit l size).isSome := by
  induction l with
  | nil => simp at h
  | cons c cs ih =>
    unfold firstFit
    by_cases hc : size ≤ c
    · simp [hc]
    · obtain ⟨d, hd, hfit⟩ := h
      have : d ∈ cs := by
        rcases List.mem_cons.mp hd with rfl | hcs
        · exact absurd hfit hc
        · exact hcs
      simpa [hc] using ih ⟨d, this, hfit⟩

/-- `firstFit` answers none when no size of the list fits. -/
theorem firstFit_none {l : List Nat} {size : Nat} (h : ∀ c ∈ l, c < size) :
    firstFit l size = none := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    unfold firstFit
    have hc : ¬size ≤ c := Nat.not_le.mpr (h c (List.mem_cons_self ..))
    simp [hc, ih (fun d hd => h d (List.mem_cons_of_mem c hd))]

/-- Every node of 1 to 1024 bytes aligned to at most 16 takes a class, the smallest that fits. -/
theorem classOf_fits {size align : Nat} (h0 : 0 < size) (h1 : size ≤ 1024)
    (ha : align ≤ classAlign) :
    ∃ i, classOf size align = some i ∧ ∃ hi : i < classSizes.length,
      size ≤ classSizes[i] ∧ ∀ j (hj : j < i), classSizes[j]'(Nat.lt_trans hj hi) < size := by
  have hsome : (firstFit classSizes size).isSome :=
    firstFit_isSome ⟨1024, by simp [classSizes], h1⟩
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨i, ?_, firstFit_some hi⟩
  simp only [classOf, hi]
  have : ¬(size = 0 ∨ classAlign < align) := by omega
  simp [this]

/-- A node larger than the largest class takes none. -/
theorem classOf_large {size align : Nat} (h : 1024 < size) : classOf size align = none := by
  have hmax : ∀ c ∈ classSizes, c ≤ 1024 := by decide
  have hnone : firstFit classSizes size = none :=
    firstFit_none (fun c hc => Nat.lt_of_le_of_lt (hmax c hc) h)
  simp [classOf, hnone]

/-- A node aligned to more than 16 takes no class: a block is aligned to 16 only. -/
theorem classOf_overaligned {size align : Nat} (h : classAlign < align) :
    classOf size align = none := by
  simp [classOf, h]

/-- The class sizes grow, and each is a multiple of 16: every block is aligned to 16. -/
theorem classSizes_sorted_and_aligned :
    classSizes.Pairwise (· < ·) ∧ ∀ c ∈ classSizes, c % classAlign = 0 := by
  decide

/-! ## The rings' arithmetic -/

/-- The word size: tickets and turn words are `u64`s. -/
def W : Nat := 2 ^ 64

/-- `DEPOT_SLOTS`. -/
def slots : Nat := 16

/-- `a.wrapping_sub(b)` on two words. -/
def wrappingSub (a b : Nat) : Nat := (a + W - b) % W

/-- `d as isize`: a word read as a signed number. -/
def asSigned (d : Nat) : Int := if d < 2 ^ 63 then d else (d : Int) - W

/-- `turn_of(t)`: the first ticket of `t`'s round of the ring. -/
def turnOf (t : Nat) : Nat := t - t % slots

/-- The wrapped difference of two words read as a signed number is the difference of the true
counts they wrap, while those are fewer than `2^63` apart: the sign a push or a pop branches on
is the true one. -/
theorem signed_exact {A B : Nat} (h1 : A < B + 2 ^ 63) (h2 : B < A + 2 ^ 63) :
    asSigned (wrappingSub (A % W) (B % W)) = (A : Int) - B := by
  unfold asSigned
  by_cases hd : wrappingSub (A % W) (B % W) < 2 ^ 63
  · rw [ite_eq_left hd]
    simp only [wrappingSub, W, Nat.reducePow] at hd h1 h2 ⊢
    omega
  · rw [ite_eq_right hd]
    simp only [wrappingSub, W, Nat.reducePow] at hd h1 h2 ⊢
    omega

/-- The turn of a wrapped ticket is the wrapped turn of the ticket: the ring's size divides the
word's range. -/
theorem turnOf_wrap (T : Nat) : turnOf (T % W) = turnOf T % W := by
  simp only [turnOf, slots, W, Nat.reducePow]
  omega

/-- What a push of ticket `t` reads in its slot's word `w`, as the code branches: equal to the
turn, it may take the slot; below, the slot still holds the previous round's magazine (the ring
is full); above, another push took this ticket (reload it). -/
inductive PushReads where
  | take
  | full
  | reload
  deriving DecidableEq, Repr

def pushReads (w t : Nat) : PushReads :=
  if w = turnOf t then .take else if w < turnOf t then .full else .reload

/-- What a pop of ticket `t` reads: one more than the turn, it may take the magazine; below, no
push filled this round yet (the ring is empty); above, another pop took this ticket. -/
inductive PopReads where
  | take
  | empty
  | reload
  deriving DecidableEq, Repr

def popReads (w t : Nat) : PopReads :=
  if w = turnOf t + 1 then .take else if w < turnOf t + 1 then .empty else .reload

/-- A slot's word for a ticket `t` of its turn is one of four: the previous round's magazine
waiting for its pop, this round waiting for its push, this round's magazine, or the slot handed
to the next round. The push and the pop each tell them apart as the code needs. -/
theorem slot_states (t : Nat) (h : slots ≤ t) :
    pushReads (turnOf t - slots + 1) t = .full ∧ pushReads (turnOf t) t = .take ∧
    pushReads (turnOf t + 1) t = .reload ∧ pushReads (turnOf t + slots) t = .reload ∧
    popReads (turnOf t - slots + 1) t = .empty ∧ popReads (turnOf t) t = .empty ∧
    popReads (turnOf t + 1) t = .take ∧ popReads (turnOf t + slots) t = .reload := by
  have hr : t % 16 < 16 := Nat.mod_lt t (by decide)
  have e : turnOf t = t - t % 16 := rfl
  have es : slots = 16 := rfl
  have ht : 16 ≤ turnOf t := by rw [e]; rw [es] at h; omega
  unfold pushReads popReads
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ite_eq_right (by rw [es]; omega), ite_eq_left (by rw [es]; omega)]
  · rw [ite_eq_left rfl]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right (by rw [es]; omega), ite_eq_right (by rw [es]; omega)]
  · rw [ite_eq_right (by rw [es]; omega), ite_eq_left (by rw [es]; omega)]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_left rfl]
  · rw [ite_eq_right (by rw [es]; omega), ite_eq_right (by rw [es]; omega)]

/-! ## The slab layer's chunks -/

/-- `CHUNK_BYTES`: a chunk's size, and its alignment. -/
def chunkBytes : Nat := 8192

/-- `chunk_of(block)`: the address masked down to the chunk's alignment, `a & !(CHUNK_BYTES - 1)`,
which is `a` less its remainder by the (power of two) chunk size. -/
def chunkOf (a : Nat) : Nat := a - a % chunkBytes

/-- `capacity(class)` for a header of `header` bytes. -/
def capacity (header size : Nat) : Nat := (chunkBytes - header) / size

/-- Every block carved from a chunk finds its chunk by `chunk_of`: a chunk is aligned to its size
and a block lies within it. -/
theorem chunkOf_block {base off : Nat} (hb : base % chunkBytes = 0) (ho : off < chunkBytes) :
    chunkOf (base + off) = base := by
  simp only [chunkOf, chunkBytes] at hb ho ⊢
  omega

/-- With a header of at most 128 bytes, every class's chunk holds at least two blocks (seven of the
largest), and the `i`-th block, `header + i * size` bytes in, lies wholly inside the chunk. -/
theorem capacity_fits {header : Nat} (hh : header ≤ 128) :
    ∀ size ∈ classSizes, 2 ≤ capacity header size ∧
      ∀ i < capacity header size, header + i * size + size ≤ chunkBytes := by
  intro size hs
  have hall : ∀ c ∈ classSizes, 0 < c ∧ c ≤ 1024 := by decide
  have hpos : 0 < size := (hall size hs).1
  have hmax : size ≤ 1024 := (hall size hs).2
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [capacity, chunkBytes]
    exact (Nat.le_div_iff_mul_le hpos).mpr (by omega)
  · simp only [capacity, chunkBytes] at hi ⊢
    have := (Nat.lt_div_iff_mul_lt hpos).mp hi
    have : (i + 1) * size ≤ 8192 - header := by
      have h2 := Nat.div_mul_le_self (8192 - header) size
      have h3 : (i + 1) * size ≤ (8192 - header) / size * size :=
        Nat.mul_le_mul_right size hi
      omega
    rw [Nat.succ_mul] at this
    omega

/-- A block `header + i * size` bytes into an aligned chunk is aligned to 16, when the header is a
multiple of 16 (the code rounds it up) and the size is a class's. -/
theorem block_aligned {base header i size : Nat} (hb : base % chunkBytes = 0)
    (hh : header % classAlign = 0) (hs : size ∈ classSizes) :
    (base + header + i * size) % classAlign = 0 := by
  have hsz : size % 16 = 0 := (classSizes_sorted_and_aligned.2 size hs)
  simp only [chunkBytes, classAlign] at hb hh hsz ⊢
  have : (i * size) % 16 = 0 := by
    rw [Nat.mul_mod, hsz]; simp
  omega

/-- `REFILL_BYTES` and `refill_count(class)`: the blocks a refill takes, about 2 KiB of them, at
least one and at most a magazine's. -/
def refillCount (size : Nat) : Nat := max 1 (min (2048 / size) 32)

theorem refillCount_bounds (size : Nat) : 1 ≤ refillCount size ∧ refillCount size ≤ 32 := by
  simp only [refillCount]
  omega

/-! ## The bound -/

/-- `ROUNDS`: the blocks a magazine holds. -/
def rounds : Nat := 32

/-- The blocks a list of magazines holds when none holds more than `rounds`. -/
theorem magazines_hold_at_most {lens : List Nat} (h : ∀ n ∈ lens, n ≤ rounds) :
    lens.sum ≤ lens.length * rounds := by
  induction lens with
  | nil => simp
  | cons n ns ih =>
    simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
    have := h n (List.mem_cons_self ..)
    have := ih (fun m hm => h m (List.mem_cons_of_mem n hm))
    omega

/-- Per class, a thread holds two magazines and the depot's full ring `slots` of them: so the
cache holds at most `2 * rounds` blocks per thread and `slots * rounds` in the depot. -/
theorem class_bound {threadLens depotLens : List Nat} (ht : threadLens.length ≤ 2)
    (hd : depotLens.length ≤ slots) (hm : ∀ n ∈ threadLens ++ depotLens, n ≤ rounds) :
    threadLens.sum ≤ 2 * rounds ∧ depotLens.sum ≤ slots * rounds := by
  have h1 := magazines_hold_at_most (fun n hn => hm n (List.mem_append_left _ hn))
  have h2 := magazines_hold_at_most (fun n hn => hm n (List.mem_append_right _ hn))
  constructor
  · exact Nat.le_trans h1 (Nat.mul_le_mul_right rounds ht)
  · exact Nat.le_trans h2 (Nat.mul_le_mul_right rounds hd)

/-- The crate docs' numbers: 64-byte nodes take 4 KiB per thread and 32 KiB in the depot. -/
theorem bound_for_64_byte_nodes : 2 * rounds * 64 = 4096 ∧ slots * rounds * 64 = 32768 := by
  decide

/-! ## The order a refill hands its blocks out in

`Pair::refill` takes `refillCount` blocks from the slab layer one after another. It hands out the
first (`carved 0`), then for `i` from `rest - 1` down to `0`, with `rest = refillCount - 1`, stores
the next block in slot `i` of the empty magazine `loaded`, and sets the magazine's length to
`rest`. A pop takes the slot just below the length. -/

/-- Slot `i` of `loaded` after the first `n` steps of the refill's loop, from the slots `before`
it: step `n` stores `carved (n + 1)` in slot `rest - 1 - n`. -/
def refillLoop {α : Type} (rest : Nat) (carved before : Nat → α) : Nat → Nat → α
  | 0, i => before i
  | n + 1, i => if i = rest - 1 - n then carved (n + 1) else refillLoop rest carved before n i

/-- The slot the `k`-th pop of a magazine of length `len` reads, with no push in between. -/
def popSlot (len k : Nat) : Nat := len - 1 - k

/-- After `n` steps, slot `rest - 1 - j` holds the block taken at step `j`, for every `j < n`. -/
theorem refillLoop_slot {α : Type} {rest n j : Nat} (carved before : Nat → α) (hn : n ≤ rest)
    (hj : j < n) : refillLoop rest carved before n (rest - 1 - j) = carved (j + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [refillLoop]
    by_cases h : j = n
    · subst h; simp
    · have hne : rest - 1 - j ≠ rest - 1 - n := by omega
      rw [ite_eq_right hne]
      exact ih (by omega) (by omega)

/-- The loop writes no slot at or past `rest`: the rest of the magazine is as it was. -/
theorem refillLoop_above {α : Type} {rest n i : Nat} (carved before : Nat → α) (hn : n ≤ rest)
    (hi : rest ≤ i) : refillLoop rest carved before n i = before i := by
  induction n with
  | zero => simp only [refillLoop]
  | succ n ih =>
    have hne : i ≠ rest - 1 - n := by omega
    simp only [refillLoop]
    rw [ite_eq_right hne]
    exact ih (by omega)

/-- The allocations after a refill take its blocks in the order the slab layer handed them out:
the refill's own allocation `carved 0`, then the `k`-th pop `carved (k + 1)`. -/
theorem refill_pops_in_carving_order {α : Type} {rest k : Nat} (carved before : Nat → α)
    (hk : k < rest) : refillLoop rest carved before rest (popSlot rest k) = carved (k + 1) := by
  unfold popSlot
  exact refillLoop_slot carved before (Nat.le_refl rest) hk

/-- The blocks a refill leaves in `loaded` fit in it. -/
theorem refill_fits (size : Nat) : refillCount size - 1 < rounds := by
  have := (refillCount_bounds size).2
  simp only [rounds]
  omega

/-- `SlabClass::alloc` carves block `n` of a chunk at `base + header + n * size`: blocks carved
one after another lie at rising addresses, so a refill from a fresh chunk hands them out rising. -/
theorem carve_rises {base header size n : Nat} (hs : 0 < size) :
    base + header + n * size < base + header + (n + 1) * size := by
  rw [Nat.succ_mul]
  omega

end Kovan.Magazine
