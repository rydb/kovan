/-!
# The STM's lock words and version clock

This file checks the arithmetic `kovan_stm` (`kovan-stm/src/var.rs`, `transaction.rs`, `lib.rs`)
rests on. The TLA+ model in `proofs/tla/stm` checks how transactions interleave; it keeps a
variable's lock word as a pair (a lock bit and a version) and renames every number of the version
clock to its rank among the numbers in use. Here the code's own words are taken as they are: 64
bits, the lock in bit 0, the clock moved by 2.

## The story in plain words

1. A variable's lock word holds its version in bits 1 to 63 and its lock in bit 0.
   `load_version_lock` reads the lock as `val & 1 == 1` and the version as `val & !1`: for an even
   version and either lock bit, it gives back exactly the two that were packed.
2. A commit locks a word it read unlocked with a compare-and-swap to `current | 1`: the same
   version, locked. An aborting commit clears the bit with `fetch_and(!1)`: the same version,
   unlocked. A commit that publishes stores its write version, which is even: unlocked, at that
   version. The commit compares the raw word it locked with the version it read, which is right
   because a word with the lock bit clear is its version.
3. The clock starts at 0 and moves by 2 at every fetch-add, so it stays even, also when it wraps
   modulo `2^64`, and every version stored is a clock value plus 2: a version never touches the
   lock bit.
4. Until the clock has moved `2^63` times it has not wrapped: each fetch-add returns more than
   every one before it, and the write version, the value returned plus 2, does not overflow. At
   `2^63` fetch-adds it wraps to 0; at a billion commit attempts a second that takes about 292
   years.
5. A load retries when the version it finds is newer than its read version. For a version a commit
   wrote, that is exactly when the commit's fetch-add came after the load of the clock that gave
   the read version.
6. Every decision of the protocol compares two of its numbers (`>`, `!=`). Renaming each number in
   use to its rank among them keeps every such comparison, which is what lets the TLA+ model
   rename them at every fetch-add and keep the clock small.

## What the model leaves out

Words are numbers below `2^64`, with the code's `&`, `|` and `!1` as Lean's bitwise operations on
them; `!1` is `2^64 - 2`. Which thread wins a lock, and when, is the TLA+ model's business.
Nothing here is about memory ordering.
-/

namespace Kovan.Stm

/-! ## The lock word -/

/-- `u64`: lock words and the clock are 64 bits. -/
def W : Nat := 2 ^ 64

/-- `!1` on a `u64`: every bit but bit 0. -/
def notOne : Nat := W - 2

/-- `load_version_lock`: the lock bit, `val & 1 == 1`, and the version, `val & !1`. -/
def decode (val : Nat) : Bool × Nat := (val &&& 1 == 1, val &&& notOne)

/-- A version and a lock bit in one word. -/
def pack (v : Nat) (l : Bool) : Nat := v + l.toNat

example : decode 7 = (true, 6) := by decide
example : decode 6 = (false, 6) := by decide
example : decode (W - 1) = (true, W - 2) := by decide

theorem and_one (w : Nat) : w &&& 1 = w % 2 := by
  simp

/-- `val & !1` clears bit 0 of a word: it is the word less its lock bit. -/
theorem and_notOne {w : Nat} (h : w < W) : w &&& notOne = w - w % 2 := by
  have hn : notOne = (2 ^ 63 - 1) <<< 1 := by decide
  have hw : w - w % 2 = (w >>> 1) <<< 1 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  rw [hn, hw]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : 1 ≤ i
  · have hs : 1 + (i - 1) = i := by omega
    by_cases hl : i < 64
    · simp [hi, hs, show i - 1 < 63 by omega]
    · have hz : w.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hs, hz]
  · simp [hi]

/-- An even version packed with either lock bit decodes to that bit and that version. -/
theorem decode_pack {v : Nat} (l : Bool) (hv : v % 2 = 0) (h : v < W) :
    decode (pack v l) = (l, v) := by
  have hW : W = 18446744073709551616 := by decide
  have hlt : pack v l < W := by
    rw [hW] at h ⊢
    cases l <;> simp [pack] <;> omega
  have h1 : pack v l % 2 = l.toNat := by cases l <;> simp [pack] <;> omega
  simp only [decode, and_one, and_notOne hlt, h1]
  cases l <;> rfl

/-- The commit's store of its write version: an even version, stored unlocked. -/
theorem store_unlocked {v : Nat} (hv : v % 2 = 0) (h : v < W) : decode v = (false, v) := by
  have := decode_pack false hv h
  simpa [pack] using this

/-- The compare-and-swap's new word, `current | 1`, of a word read unlocked: the same version,
plus the lock bit. -/
theorem lock_word {v : Nat} (hv : v % 2 = 0) : v ||| 1 = v + 1 := by
  have h := Nat.two_pow_add_eq_or_of_lt (show 1 < 2 ^ 1 by decide) (v / 2)
  rw [Nat.pow_one] at h
  have hv2 : v = 2 * (v / 2) := by omega
  rw [hv2]
  exact h.symm

theorem cas_locks {v : Nat} (hv : v % 2 = 0) (h : v < W) : decode (v ||| 1) = (true, v) := by
  have := decode_pack true hv h
  simp only [pack, Bool.toNat_true] at this
  rw [lock_word hv]
  exact this

/-- `fetch_and(!1)`, an aborting commit's release: whatever the word, the lock bit cleared and the
version kept. -/
theorem unlock_keeps_version {w : Nat} (h : w < W) :
    decode (w &&& notOne) = (false, (decode w).2) := by
  have hm : w &&& notOne = w - w % 2 := and_notOne h
  have he : (w - w % 2) % 2 = 0 := by omega
  have hl : w - w % 2 < W := by omega
  show decode (w &&& notOne) = (false, w &&& notOne)
  rw [hm]
  exact store_unlocked he hl

/-- A word with its lock bit clear is its version, so the commit may compare the raw word it
locked (`current > read_entry.version`) with the version it read. -/
theorem unlocked_word_is_version {w : Nat} (h : w < W) (hl : (decode w).1 = false) :
    w = (decode w).2 := by
  have h0 : w % 2 ≠ 1 := by
    simp only [decode, and_one] at hl
    simpa using hl
  show w = w &&& notOne
  rw [and_notOne h]
  omega

/-! ## The version clock -/

/-- The clock after `n` fetch-adds of 2, modulo `2^64`; the `n + 1`-th fetch-add returns this. -/
def clockAfter (n : Nat) : Nat := 2 * n % W

/-- The clock stays even, wrapping included: no version stored ever carries the lock bit. -/
theorem clock_even (n : Nat) : clockAfter n % 2 = 0 := by
  simp only [clockAfter, W, Nat.reducePow]
  omega

theorem clock_no_wrap {n : Nat} (h : n < 2 ^ 63) : clockAfter n = 2 * n := by
  simp only [clockAfter, W, Nat.reducePow] at h ⊢
  omega

/-- Each fetch-add returns more than every one before it, until `2^63` of them. -/
theorem clock_grows {n m : Nat} (h1 : n < m) (h2 : m < 2 ^ 63) : clockAfter n < clockAfter m := by
  rw [clock_no_wrap (by omega), clock_no_wrap h2]
  omega

/-- The write version, the value a fetch-add returned plus 2, is the clock after that
fetch-add, and fits the word, until `2^63` fetch-adds. -/
theorem write_version {n : Nat} (h : n + 1 < 2 ^ 63) :
    clockAfter n + 2 = clockAfter (n + 1) ∧ clockAfter n + 2 < W := by
  rw [clock_no_wrap (by omega), clock_no_wrap h]
  simp only [W, Nat.reducePow] at h ⊢
  omega

/-- The ceiling: the `2^63`-th fetch-add wraps the clock to 0, and from there the versions no
longer compare as the commits' order. -/
theorem clock_wraps : clockAfter (2 ^ 63) = 0 := by decide

/-- A load reads the clock after `m` fetch-adds (its read version), then finds a version written
by the commit whose fetch-add was the `k + 1`-th: it retries, the version being newer than the read
version, exactly when that fetch-add came after the load. -/
theorem retry_iff_later {k m : Nat} (hk : k < 2 ^ 63) (hm : m < 2 ^ 63) :
    clockAfter m < clockAfter k + 2 ↔ m ≤ k := by
  rw [clock_no_wrap hk, clock_no_wrap hm]
  omega

/-- The same on the values themselves: with even `g` (what the commit's fetch-add returned) and
`r` (the read version), the version `g + 2` is newer than `r` exactly when `g` is at least `r`. -/
theorem newer_iff {g r : Nat} (hg : g % 2 = 0) (hr : r % 2 = 0) : r < g + 2 ↔ r ≤ g := by
  omega

/-! ## Renaming the numbers to their ranks -/

/-- The rank of `n` among the numbers in use, `L`: how many of them are smaller. -/
def rank (L : List Nat) (n : Nat) : Nat := (L.filter (· < n)).length

theorem rank_cons_lt {x n : Nat} (L : List Nat) (h : x < n) : rank (x :: L) n = rank L n + 1 := by
  simp [rank, h]

theorem rank_cons_ge {x n : Nat} (L : List Nat) (h : ¬x < n) : rank (x :: L) n = rank L n := by
  simp [rank, h]

theorem rank_mono {L : List Nat} {a b : Nat} (h : a ≤ b) : rank L a ≤ rank L b := by
  induction L with
  | nil => simp [rank]
  | cons x L ih =>
    by_cases hx : x < a
    · rw [rank_cons_lt L hx, rank_cons_lt L (by omega)]
      omega
    · by_cases hb : x < b
      · rw [rank_cons_ge L hx, rank_cons_lt L hb]
        omega
      · rw [rank_cons_ge L hx, rank_cons_ge L hb]
        omega

/-- A number in use ranks below every larger one. -/
theorem rank_lt {L : List Nat} {a b : Nat} (ha : a ∈ L) (h : a < b) : rank L a < rank L b := by
  induction L with
  | nil => simp at ha
  | cons x L ih =>
    rcases List.mem_cons.mp ha with rfl | hm
    · have := rank_mono (L := L) (Nat.le_of_lt h)
      rw [rank_cons_ge L (Nat.lt_irrefl _), rank_cons_lt L h]
      omega
    · have := ih hm
      by_cases hx : x < a
      · rw [rank_cons_lt L hx, rank_cons_lt L (by omega)]
        omega
      · by_cases hb : x < b
        · rw [rank_cons_ge L hx, rank_cons_lt L hb]
          omega
        · rw [rank_cons_ge L hx, rank_cons_ge L hb]
          omega

/-- Renaming keeps every `<` between numbers in use (so every `>`). -/
theorem rank_lt_iff {L : List Nat} {a b : Nat} (ha : a ∈ L) :
    rank L a < rank L b ↔ a < b := by
  constructor
  · intro h
    by_cases hab : a < b
    · exact hab
    · have := rank_mono (L := L) (Nat.le_of_not_lt hab)
      omega
  · exact rank_lt ha

/-- Renaming keeps every `=` and `!=` between numbers in use. -/
theorem rank_eq_iff {L : List Nat} {a b : Nat} (ha : a ∈ L) (hb : b ∈ L) :
    rank L a = rank L b ↔ a = b := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · have := rank_lt ha hab
      omega
    · exact hab
    · have := rank_lt hb hab
      omega
  · intro h
    rw [h]

end Kovan.Stm
