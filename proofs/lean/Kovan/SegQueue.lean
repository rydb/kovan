/-!
# The segment queue's words, positions and length

This file checks the arithmetic `SegQueue` (`kovan-queue/src/seg_queue.rs`) rests on. The TLA+
model in `proofs/tla/segqueue` checks the concurrent steps; it counts segment ids without
wrapping and cells in small segments. Here the code's own bit layout is taken as it is: 44 bits
of segment id, 20 bits of index, 32 cells per segment, positions modulo `2^49`.

## The story in plain words

Each end of the queue keeps one claim word: a segment id in the high 44 bits and an index in the
low 20 bits. A push claims a cell with one fetch-add on the tail word, a pop with one fetch-add on
the head word. The cell a claim names has a queue position, `id * 32 + index`, which is the order
every thread agrees on.

1. A fetch-add raises the index by one and never carries into the id, as long as the index stays
   below `2^20` (it stays below 32 plus the number of threads).
2. The position of a claim word is the position counted without wrapping, taken modulo `2^49`;
   claims of cells get distinct positions, in the order of their words, and none of the word's
   moves (a fetch-add, the tail's move to the successor's second cell, the head's move to the
   successor's first cell) ever takes the position back.
3. `behind`, the comparison of two ids modulo `2^44`, says exactly which id is the earlier one
   while the two are fewer than `2^43` apart.
4. `classify` gives the same answer on the code's wrapped ids as on ids counted without wrapping,
   while the head word is at most one segment ahead of the tail word (the TLA+ model checks that
   every state keeps it so, `Words`). An `Empty` answer means every cell pushes had claimed by
   then lies behind the head word, so pops had claimed it; a `Claimed` answer names a cell of the
   segment; a `Drained` answer comes only once every cell of the head's segment is claimed.
5. `len`, `back - front` modulo `2^49` with anything past half the space read as 0, is the number
   of cells pushes claimed and pops did not, while the head is behind the tail by less than
   `2^48`, and 0 while pops ran ahead of pushes by at most `2^48`.

## What the model leaves out

The words are numbers, with the code's masks, shifts and ors as Lean's bitwise operations on
them; the code's `u64` arithmetic never overflows on the values it computes here except in
`wrapping_sub`, modelled as a subtraction modulo `2^64`. Nothing here is about threads.
-/

namespace Kovan.SegQueue

/-! ## The claim words -/

/-- `SEGMENT_SIZE`: the cells of one segment. -/
def segmentSize : Nat := 32

/-- `INDEX_MASK`: the low 20 bits of a claim word hold the index. -/
def indexMask : Nat := 2 ^ 20 - 1

/-- `ID_MASK`, `u64::MAX >> INDEX_BITS`: segment ids are counted modulo `2^44`. -/
def idMask : Nat := 2 ^ 44 - 1

/-- `POS_MASK`, `(ID_MASK << SEGMENT_SHIFT) | (SEGMENT_SIZE - 1)`: positions are counted modulo
`2^49`. -/
def posMask : Nat := (idMask <<< 5) ||| 31

/-- `word(id, index)`: the claim word naming cell `index` of segment `id`. -/
def word (id index : Nat) : Nat := ((id &&& idMask) <<< 20) ||| index

/-- `id_of(w)`: the segment id of a claim word. -/
def idOf (w : Nat) : Nat := w >>> 20

/-- `index_of(w)`: the index of a claim word. -/
def indexOf (w : Nat) : Nat := w &&& indexMask

/-- `next_id(id)`: the id after `id`, modulo `2^44`. -/
def nextId (id : Nat) : Nat := (id + 1) &&& idMask

/-- `behind(a, b)`: `true` when segment id `a` is behind `b`. The `u64` `wrapping_sub` is a
subtraction modulo `2^64`. -/
def behind (a b : Nat) : Bool :=
  let d := ((b + 2 ^ 64 - a) % 2 ^ 64) &&& idMask
  d != 0 && d < 2 ^ 43

/-- `position(w)`: the queue position of a claim word, the claims past the segment's end capped
at its end. -/
def position (w : Nat) : Nat := ((idOf w <<< 5) + min (indexOf w) segmentSize) &&& posMask

theorem posMask_eq : posMask = 2 ^ 49 - 1 := by decide

theorem mask_mod (x : Nat) : x &&& idMask = x % 2 ^ 44 := Nat.and_two_pow_sub_one_eq_mod x 44

/-- A claim word is the id, modulo `2^44`, times `2^20`, plus the index: the or of the two never
mixes their bits. -/
theorem word_eq {index : Nat} (id : Nat) (h : index < 2 ^ 20) :
    word id index = 2 ^ 20 * (id % 2 ^ 44) + index := by
  unfold word
  rw [mask_mod, Nat.shiftLeft_eq, Nat.mul_comm, Nat.two_pow_add_eq_or_of_lt h]

theorem idOf_word {index : Nat} (id : Nat) (h : index < 2 ^ 20) :
    idOf (word id index) = id % 2 ^ 44 := by
  rw [idOf, word_eq id h, Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at h ⊢
  omega

theorem indexOf_word {index : Nat} (id : Nat) (h : index < 2 ^ 20) :
    indexOf (word id index) = index := by
  rw [indexOf, indexMask, Nat.and_two_pow_sub_one_eq_mod, word_eq id h]
  simp only [Nat.reducePow] at h ⊢
  omega

/-- A claim word fits the 64 bits of the code's `AtomicU64`. -/
theorem word_lt {index : Nat} (id : Nat) (h : index < 2 ^ 20) : word id index < 2 ^ 64 := by
  rw [word_eq id h]
  simp only [Nat.reducePow] at h ⊢
  omega

/-- The fetch-add on a claim word raises its index by one and leaves the id as it is. -/
theorem word_add_one {index : Nat} (id : Nat) (h : index + 1 < 2 ^ 20) :
    word id index + 1 = word id (index + 1) := by
  rw [word_eq id (by omega), word_eq id h]
  omega

/-- The index never carries into the id: a word is moved to the next segment before it claims
again, so its index stays below `SEGMENT_SIZE` plus the threads that claim at once, and kovan
hands out at most 65,536 thread ids. -/
theorem fetch_add_keeps_id {index : Nat} (id : Nat) (h : index ≤ segmentSize + 65536) :
    idOf (word id index + 1) = id % 2 ^ 44 ∧ indexOf (word id index + 1) = index + 1 := by
  have h' : index + 1 < 2 ^ 20 := by
    simp only [segmentSize] at h
    simp only [Nat.reducePow]
    omega
  rw [word_add_one id h']
  exact ⟨idOf_word id h', indexOf_word id h'⟩

theorem nextId_eq (id : Nat) : nextId id = (id + 1) % 2 ^ 44 := mask_mod (id + 1)

/-! ## Positions -/

/-- The position of cell `index` of segment `s`, with ids counted without wrapping. An index past
the segment's end counts as its end. Example: `pos 2 5 = 69`; `pos 2 40 = pos 3 0 = 96`. -/
def pos (s index : Nat) : Nat := s * segmentSize + min index segmentSize

example : pos 2 5 = 69 := rfl
example : pos 2 40 = pos 3 0 := rfl

/-- The code's position of a claim word is the position counted without wrapping, modulo `2^49`:
the id's wrap at `2^44` is the position's wrap at `2^49`. -/
theorem position_word {index : Nat} (id : Nat) (h : index < 2 ^ 20) :
    position (word id index) = pos id index % 2 ^ 49 := by
  rw [position, posMask_eq, Nat.and_two_pow_sub_one_eq_mod, idOf_word id h, indexOf_word id h,
    Nat.shiftLeft_eq, pos]
  simp only [segmentSize, Nat.reducePow] at h ⊢
  omega

/-- Two cells (indexes below the segment's end) at the same position are the same cell. -/
theorem pos_inj {s t i j : Nat} (hi : i < segmentSize) (hj : j < segmentSize)
    (h : pos s i = pos t j) : s = t ∧ i = j := by
  simp only [pos, segmentSize] at hi hj h
  have hs : s = t := by
    rcases Nat.lt_trichotomy s t with hlt | heq | hgt
    · have : s * 32 + 32 ≤ t * 32 := by
        have := Nat.mul_le_mul_right 32 (Nat.succ_le_of_lt hlt)
        simpa [Nat.succ_mul] using this
      omega
    · exact heq
    · have : t * 32 + 32 ≤ s * 32 := by
        have := Nat.mul_le_mul_right 32 (Nat.succ_le_of_lt hgt)
        simpa [Nat.succ_mul] using this
      omega
  subst hs
  exact ⟨rfl, by omega⟩

/-- Positions follow the order of the words: a word earlier in segment order, or in the same
segment with a smaller index below the end, names an earlier position. -/
theorem pos_lt {s t i j : Nat} (hi : i < segmentSize)
    (h : s < t ∨ (s = t ∧ i < j)) : pos s i < pos t j := by
  simp only [pos, segmentSize] at hi ⊢
  rcases h with hlt | ⟨rfl, hij⟩
  · have : s * 32 + 32 ≤ t * 32 := by
      have := Nat.mul_le_mul_right 32 (Nat.succ_le_of_lt hlt)
      simpa [Nat.succ_mul] using this
    omega
  · omega

/-- A fetch-add never takes the position back, and moves it on while the index is below the end. -/
theorem pos_fetch_add (s i : Nat) :
    pos s i ≤ pos s (i + 1) ∧ (i < segmentSize → pos s i < pos s (i + 1)) := by
  simp only [pos, segmentSize]
  omega

/-- The tail word's move past full segment `s`, to the successor's second cell: the successor's
first cell, at the position right after `s`, holds the value of the push that linked it. -/
theorem pos_tail_advance (s i : Nat) (h : segmentSize ≤ i) :
    pos s i = pos (s + 1) 0 ∧ pos s i < pos (s + 1) 1 := by
  simp only [pos, segmentSize, Nat.succ_mul] at h ⊢
  omega

/-- The head word's move past drained segment `s`, to the successor's first cell, keeps the
position. -/
theorem pos_head_advance (s i : Nat) (h : segmentSize ≤ i) : pos s i = pos (s + 1) 0 :=
  (pos_tail_advance s i h).1

/-! ## Comparing segment ids -/

/-- `behind` on the code's wrapped ids says which of two ids counted without wrapping is the
earlier one, while they are fewer than `2^43` apart. -/
theorem behind_iff {a b : Nat} (hab : a < b + 2 ^ 43) (hba : b < a + 2 ^ 43) :
    behind (a % 2 ^ 44) (b % 2 ^ 44) = true ↔ a < b := by
  simp only [behind, mask_mod, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Nat.reducePow] at hab hba ⊢
  omega

/-! ## What the two words say -/

/-- What `classify` answers. -/
inductive View where
  | empty
  | claimed
  | drained
  deriving DecidableEq, Repr

/-- `classify(hw, tw)` on the code's words. -/
def classifyCode (hw tw : Nat) : View :=
  if idOf tw = idOf hw then
    if indexOf hw < min (indexOf tw) segmentSize then .claimed
    else if indexOf tw ≤ segmentSize then .empty else .drained
  else if nextId (idOf tw) = idOf hw then
    if indexOf hw = 0 then .claimed else .empty
  else if indexOf hw < segmentSize then .claimed else .drained

/-- `classify` with segment ids counted without wrapping: the head word names cell `d` of
segment `sh`, the tail word cell `e` of segment `st`. -/
def classify (sh d st e : Nat) : View :=
  if st = sh then
    if d < min e segmentSize then .claimed else if e ≤ segmentSize then .empty else .drained
  else if st + 1 = sh then
    if d = 0 then .claimed else .empty
  else if d < segmentSize then .claimed else .drained

/-- The code's `classify` gives the answer of the one without wrapping while the head word is at
most one segment ahead of the tail word and fewer than `2^43` segments behind it. -/
theorem classifyCode_word {sh st d e : Nat} (hd : d < 2 ^ 20) (he : e < 2 ^ 20)
    (h1 : sh ≤ st + 1) (h2 : st < sh + 2 ^ 43) :
    classifyCode (word sh d) (word st e) = classify sh d st e := by
  have same : st % 2 ^ 44 = sh % 2 ^ 44 ↔ st = sh := by
    simp only [Nat.reducePow] at h2 ⊢
    constructor <;> intro <;> omega
  have next : (st % 2 ^ 44 + 1) % 2 ^ 44 = sh % 2 ^ 44 ↔ st + 1 = sh := by
    simp only [Nat.reducePow] at h2 ⊢
    constructor <;> intro <;> omega
  simp only [classifyCode, classify, idOf_word _ hd, idOf_word _ he, indexOf_word _ hd,
    indexOf_word _ he, nextId_eq, same, next]

/-- The cells pushes have claimed while the tail word names cell `e` of segment `st`: every
position before the tail word's, and, once the tail word is past the segment's end, the
successor's first cell, which the push that links the successor claims. -/
def PushClaimed (st e p : Nat) : Prop :=
  p < pos st e ∨ (segmentSize < e ∧ p = pos (st + 1) 0)

/-- An `Empty` answer: every cell pushes had claimed when the tail word was read lies behind the
head word, read before it; the head word only moves forward, so pops had claimed every one of
those cells at that moment. -/
theorem empty_sound {sh d st e p : Nat} (h : classify sh d st e = .empty)
    (hp : PushClaimed st e p) : p < pos sh d := by
  unfold classify at h
  unfold PushClaimed at hp
  simp only [pos, segmentSize, Nat.succ_mul] at h hp ⊢
  by_cases hs : st = sh
  · by_cases hc : d < min e 32
    · simp only [hs, hc, ↓reduceIte, reduceCtorEq] at h
    · by_cases he : e ≤ 32
      · subst hs
        omega
      · simp only [hs, hc, he, ↓reduceIte, reduceCtorEq] at h
  · by_cases hn : st + 1 = sh
    · by_cases hd : d = 0
      · simp only [hs, hn, hd, ↓reduceIte, reduceCtorEq] at h
      · subst hn
        omega
    · by_cases hd : d < 32 <;> simp only [hs, hn, hd, ↓reduceIte, reduceCtorEq] at h

/-- A `Claimed` answer names a cell of the head's segment, so the code's `cells.get(index)`
finds it. -/
theorem claimed_index_lt {sh d st e : Nat} (h : classify sh d st e = .claimed) :
    d < segmentSize := by
  unfold classify at h
  simp only [segmentSize] at h ⊢
  by_cases hs : st = sh
  · by_cases hc : d < min e 32
    · omega
    · by_cases he : e ≤ 32 <;> simp only [hs, hc, he, ↓reduceIte, reduceCtorEq] at h
  · by_cases hn : st + 1 = sh
    · by_cases hd : d = 0
      · omega
      · simp only [hs, hn, hd, ↓reduceIte, reduceCtorEq] at h
    · by_cases hd : d < 32
      · exact hd
      · simp only [hs, hn, hd, ↓reduceIte, reduceCtorEq] at h

/-- A `Drained` answer comes only once the head word's index passed the segment's end: pops have
claimed every cell of the head's segment. -/
theorem drained_full {sh d st e : Nat} (h : classify sh d st e = .drained) :
    segmentSize ≤ d := by
  unfold classify at h
  simp only [segmentSize] at h ⊢
  by_cases hs : st = sh
  · by_cases hc : d < min e 32
    · simp only [hs, hc, ↓reduceIte, reduceCtorEq] at h
    · by_cases he : e ≤ 32
      · simp only [hs, hc, he, ↓reduceIte, reduceCtorEq] at h
      · omega
  · by_cases hn : st + 1 = sh
    · by_cases hd : d = 0 <;> simp only [hs, hn, hd, ↓reduceIte, reduceCtorEq] at h
    · by_cases hd : d < 32
      · simp only [hs, hn, hd, ↓reduceIte, reduceCtorEq] at h
      · omega

/-! ## The length -/

/-- `len` on the two positions: `back - front` modulo `2^49`, read as 0 past half the space. -/
def lenOf (front back : Nat) : Nat :=
  let n := ((back + 2 ^ 64 - front) % 2 ^ 64) &&& posMask
  if n > posMask >>> 1 then 0 else n

/-- `len()`: the length the code computes from the head and the tail word. -/
def len (hw tw : Nat) : Nat := lenOf (position hw) (position tw)

theorem posMask_half : posMask >>> 1 = 2 ^ 48 - 1 := by decide

/-- While the head is behind the tail by less than `2^48` positions, `len` is the number of cells
between them: those pushes claimed and pops did not. -/
theorem lenOf_exact {f b : Nat} (hfb : f ≤ b) (hlt : b - f < 2 ^ 48) :
    lenOf (f % 2 ^ 49) (b % 2 ^ 49) = b - f := by
  simp only [lenOf, posMask_half]
  rw [posMask_eq, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.reducePow] at hlt ⊢
  have hn : ((b % 562949953421312 + 18446744073709551616 - f % 562949953421312)
      % 18446744073709551616) % 562949953421312 = b - f := by omega
  rw [hn]
  simp only [gt_iff_lt, ite_eq_right_iff]
  omega

/-- While pops ran ahead of pushes, by at most `2^48` positions (each pop that found no pushed
cell took one out of play), `len` is 0. -/
theorem lenOf_ahead {f b : Nat} (hbf : b < f) (hle : f - b ≤ 2 ^ 48) :
    lenOf (f % 2 ^ 49) (b % 2 ^ 49) = 0 := by
  simp only [lenOf, posMask_half]
  rw [posMask_eq, Nat.and_two_pow_sub_one_eq_mod]
  simp only [Nat.reducePow] at hle ⊢
  have hn : ((b % 562949953421312 + 18446744073709551616 - f % 562949953421312)
      % 18446744073709551616) % 562949953421312 = 562949953421312 - (f - b) := by omega
  rw [hn]
  simp only [gt_iff_lt, ite_eq_left_iff, Nat.not_lt]
  omega

/-- `len()` on two claim words: the cells between the head and the tail while the head is behind
by less than `2^48` positions. -/
theorem len_word {sh d st e : Nat} (hd : d < 2 ^ 20) (he : e < 2 ^ 20)
    (hfb : pos sh d ≤ pos st e) (hlt : pos st e - pos sh d < 2 ^ 48) :
    len (word sh d) (word st e) = pos st e - pos sh d := by
  rw [len, position_word _ hd, position_word _ he]
  exact lenOf_exact hfb hlt

/-- `len()` on two claim words while pops ran ahead of pushes by at most `2^48` positions. -/
theorem len_word_ahead {sh d st e : Nat} (hd : d < 2 ^ 20) (he : e < 2 ^ 20)
    (hbf : pos st e < pos sh d) (hle : pos sh d - pos st e ≤ 2 ^ 48) :
    len (word sh d) (word st e) = 0 := by
  rw [len, position_word _ hd, position_word _ he]
  exact lenOf_ahead hbf hle

end Kovan.SegQueue
