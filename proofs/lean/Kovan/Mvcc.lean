/-!
# The multi-version store's timestamps, backoff, read horizon and version chains

This file checks the arithmetic `kovan-mvcc` rests on (`kovan-mvcc/src/timestamp_oracle.rs`,
`backoff.rs`, `percolator.rs`, `storage.rs`). The TLA+ model in `proofs/tla/mvcc` checks how
transactions interleave; it counts timestamps without wrapping, folds the backoff's count and
the spin caps, and takes each version-chain call as one step. Here the code's own constants and
formulas are taken as they are: the oracle's 64-bit counter, `DefaultBackoff`'s schedule,
`safe_read_ts`'s pin, and the lookups and the garbage collection of `InMemoryStorage`'s version
chains.

## The story in plain words

1. `LocalTimestampOracle::get_timestamp` is `counter.fetch_add(1) + 1` on a `u64`. From a counter
   at `c` (`with_initial(c)`, 0 by default), call number `k` (from 0) answers `c + k + 1` while
   that is below `2^64`, so every answer is greater than every earlier one. The call that finds
   the counter at `u64::MAX` overflows its `+ 1`, and the calls after it, the counter wrapped to
   0, answer 1, 2, ... again: unique and increasing holds for `2^64 - 1 - c` calls, 584 years at
   one call per nanosecond.
2. `DefaultBackoff` answers `Yield` for attempts 0 to 2, `Retry` after sleeping
   `100 << (attempt - 3)` microseconds for attempts 3 to 7, and `Abort` from attempt 8: a read that
   keeps meeting a lock gives up at its ninth look, after 3100 microseconds of sleep, and answers
   `Err(LockConflict)`. Neither shift (nor the wasm spin's) overflows.
3. `safe_read_ts` answers at most `oracle_now`. Past its spin cap it pins below the oldest
   writer's `start_ts` `m`, answering `min(oracle_now, m.saturating_sub(1))`; either way it
   answers below the `commit_ts` of every writer still registered. It spins at most `SPIN_CAP`
   times, each time at most 64 PAUSEs, and `min_ts`'s merge of unstable passes is the least value
   any of them saw.
4. A key's records (`CF_WRITE`, a `BTreeMap` from `commit_ts`) are looked up from the top:
   `get_latest_write(key, ts)` is the greatest record at or below `ts`, `get_latest_commit` the
   greatest Put or Delete. Prewrite rejects a key when the greatest record of any kind is at or
   after its `start_ts`, which is exactly when some record is. The SSI validation fails a key when
   its greatest Put or Delete is after `start_ts`: exactly when some transaction committed it
   after `start_ts`. Before the fix it looked at the greatest record of any kind, and a Rollback
   record above a commit hid the commit (the TLA+ model's mutation `ssi_latest_record`).
5. `gc_writes(key, watermark)` keeps the greatest Put or Delete at or below the watermark and the
   records above it, and drops those below it: every read at or above the watermark finds the
   version it found before, and prewrite's check on the greatest record is unchanged. Before the
   fix it kept the greatest record of any kind, and a Rollback record took the commit under it
   (`gc_keeps_latest_record`).
6. `gc_data` keeps the data version (`CF_DATA`, from `start_ts`) that the greatest commit at or
   below the watermark names, and those above it: a read at or above the watermark still finds
   its data. Before the fix it kept the greatest data version, and a prewrite not yet committed
   took the committed version's data under it (`gc_keeps_latest_data`).

## What the model leaves out

Timestamps are numbers, and `u64` arithmetic is arithmetic modulo `2^64` where the code wraps. A
version chain is a function from timestamps to entries: the code's `BTreeMap` holds finitely many,
and `range(..=ts).next_back()` is the search from `ts` down. That a key's commits come in the
order of their `start_ts` (a commit on a key starts after the one before it committed) is the
protocol's, which the TLA+ model checks (`FirstCommitterWins`); here it is a hypothesis of the one
theorem that needs it. Nothing here is about threads or memory ordering.
-/

namespace Kovan.Mvcc

/-! ## The oracle -/

/-- `u64` arithmetic wraps modulo `2^64`. -/
def u64 : Nat := 2 ^ 64

/-- The counter after `k` calls from `c`: each `fetch_add(1)` wraps. -/
def counterAfter (c k : Nat) : Nat := (c + k) % u64

/-- Call `k`'s answer, `fetch_add(1) + 1`, before the `+ 1` is cut to 64 bits. -/
def answer (c k : Nat) : Nat := counterAfter c k + 1

theorem answer_eq {c k : Nat} (h : c + k + 1 < u64) : answer c k = c + k + 1 := by
  unfold answer counterAfter
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Every answer is greater than every earlier one, while they fit in 64 bits: unique and
increasing. -/
theorem answer_increasing {c j k : Nat} (hjk : j < k) (h : c + k + 1 < u64) :
    answer c j < answer c k := by
  rw [answer_eq (by omega), answer_eq h]
  omega

/-- The call that finds the counter at `u64::MAX`: its `+ 1` does not fit in 64 bits (a panic in
a debug build). -/
theorem answer_overflows {c : Nat} (hc : c < u64) : answer c (u64 - 1 - c) = u64 := by
  unfold answer counterAfter
  rw [show c + (u64 - 1 - c) = u64 - 1 by omega, Nat.mod_eq_of_lt (by unfold u64; omega)]
  unfold u64
  omega

/-- After the wrap the answers start again from 1: a release build hands out timestamps twice. -/
theorem answer_repeats {c j : Nat} (hc : c < u64) : answer c (u64 - c + j) = answer 0 j := by
  unfold answer counterAfter
  rw [show c + (u64 - c + j) = u64 + j by omega, Nat.add_mod_left, Nat.zero_add]

/-- From 0, at one timestamp per nanosecond, the counter wraps after 584 years. -/
theorem years_to_wrap : u64 / (10 ^ 9 * 60 * 60 * 24 * 365) = 584 := by decide

/-! ## The backoff of a read that meets a lock -/

/-- `BackoffAction`. -/
inductive Action where
  | retry
  | yield
  | abort
  deriving DecidableEq

/-- `DefaultBackoff::backoff(attempt)`. -/
def backoff (attempt : Nat) : Action :=
  if attempt < 3 then .yield else if attempt < 8 then .retry else .abort

/-- The sleep of attempts 3 to 7, `100 << (attempt - 3)` microseconds. -/
def sleepMicros (attempt : Nat) : Nat := 100 <<< (attempt - 3)

/-- The wasm build's spin instead, `64_u32 << (attempt - 3)` PAUSEs. -/
def wasmSpins (attempt : Nat) : Nat := 64 <<< (attempt - 3)

/-- A read's attempt count starts at 0 and goes up by one each time it looks again: no count
below 8 aborts, and every count from 8 does, so the read gives up at its ninth look. -/
theorem gives_up_at_ninth_look :
    (∀ a, a < 8 → backoff a ≠ .abort) ∧ (∀ a, 8 ≤ a → backoff a = .abort) := by
  constructor
  · intro a ha
    unfold backoff
    by_cases h3 : a < 3
    · simp [h3]
    · simp [h3, ha]
  · intro a ha
    unfold backoff
    simp [show ¬a < 3 by omega, show ¬a < 8 by omega]

/-- The sleeps before the read gives up: 3100 microseconds in all (after three yields). -/
theorem sleep_before_giving_up :
    sleepMicros 3 + sleepMicros 4 + sleepMicros 5 + sleepMicros 6 + sleepMicros 7 = 3100 := by
  decide

/-- Neither shift overflows: the sleep fits a `u64`, the wasm spin count a `u32`. -/
theorem shifts_fit {a : Nat} (h1 : 3 ≤ a) (h2 : a < 8) :
    sleepMicros a ≤ 1600 ∧ wasmSpins a ≤ 1024 := by
  have : a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## The read horizon of `safe_read_ts` -/

/-- `oracle_now.min(m.saturating_sub(1))`: `Nat` subtraction stops at 0 as `saturating_sub`
does. -/
def pin (now m : Nat) : Nat := min now (m - 1)

/-- One turn of `safe_read_ts`'s loop: an answer, or a spin and another `min_ts`. -/
inductive Turn where
  | answer (h : Nat)
  | spin

/-- The loop's decision on `min_ts`'s answer `m`, at spin `attempt` of `cap` (`SPIN_CAP`). -/
def turn (now : Nat) (m : Option Nat) (attempt cap : Nat) : Turn :=
  match m with
  | none => .answer now
  | some m => if now < m then .answer now else if cap ≤ attempt then .answer (pin now m) else .spin

/-- The horizon is never above `oracle_now`. -/
theorem turn_le_now {now attempt cap h : Nat} {m : Option Nat}
    (ht : turn now m attempt cap = .answer h) : h ≤ now := by
  unfold turn at ht
  cases m with
  | none => cases ht; exact Nat.le_refl _
  | some m =>
    simp only at ht
    by_cases hn : now < m
    · simp only [hn, ↓reduceIte, Turn.answer.injEq] at ht
      omega
    · by_cases hc : cap ≤ attempt
      · simp only [hn, hc, ↓reduceIte, Turn.answer.injEq] at ht
        unfold pin at ht
        omega
      · simp [hn, hc] at ht

/-- The horizon is below the `commit_ts` `c` of every registered writer: one whose `start_ts`
`s` is at least the least registered `start_ts` `m`. Timestamps start at 1, so `m ≥ 1`. -/
theorem turn_below_writers {now attempt cap h m s c : Nat}
    (ht : turn now (some m) attempt cap = .answer h) (hm : 1 ≤ m) (hs : m ≤ s) (hc : s < c) :
    h < c := by
  unfold turn at ht
  by_cases hn : now < m
  · simp only [hn, ↓reduceIte, Turn.answer.injEq] at ht
    omega
  · by_cases hcap : cap ≤ attempt
    · simp only [hn, hcap, ↓reduceIte, Turn.answer.injEq] at ht
      unfold pin at ht
      omega
    · simp [hn, hcap] at ht

/-- At spin `SPIN_CAP` the loop answers: it spins at most `SPIN_CAP` times. -/
theorem turn_at_cap (now cap : Nat) (m : Option Nat) : ∃ h, turn now m cap cap = .answer h := by
  unfold turn
  cases m with
  | none => exact ⟨now, rfl⟩
  | some m =>
    by_cases hn : now < m
    · exact ⟨now, by simp [hn]⟩
    · exact ⟨pin now m, by simp [hn]⟩

/-- Each spin's PAUSE loop, `1u32 << attempt.min(6)`, is at most 64 PAUSEs. -/
theorem pauses_le (attempt : Nat) : 1 <<< min attempt 6 ≤ 64 := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  have : min attempt 6 ≤ 6 := Nat.min_le_right _ _
  calc 2 ^ min attempt 6 ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) this
    _ = 64 := by decide

/-- `min_ts`'s merge of an unstable pass into the least value seen so far. -/
def merge : Option Nat → Option Nat → Option Nat
  | none, m => m
  | c, none => c
  | some c, some m => some (min c m)

/-- The merge is at or below every value it was given: a writer any pass saw pins the answer. -/
theorem merge_le {a b : Option Nat} {x : Nat} (hx : a = some x ∨ b = some x) :
    ∃ y, merge a b = some y ∧ y ≤ x := by
  cases a with
  | none =>
    cases b with
    | none => simp at hx
    | some m => simp at hx; exact ⟨m, rfl, by omega⟩
  | some c =>
    cases b with
    | none => simp at hx; exact ⟨c, rfl, by omega⟩
    | some m =>
      refine ⟨min c m, rfl, ?_⟩
      rcases hx with h | h <;> simp at h <;> omega

/-! ## Version chains -/

/-- The kind of a record: `WriteKind`. -/
inductive Kind where
  | put
  | del
  | rb
  deriving DecidableEq

/-- `WriteInfo`: the record's kind and the `start_ts` of the data it names. -/
structure Rec where
  kind : Kind
  start : Nat
  deriving DecidableEq

/-- A Put or a Delete: what `get_latest_commit` keeps and a Rollback record is not. -/
def isCommit : Option Rec → Bool
  | some ⟨.put, _⟩ => true
  | some ⟨.del, _⟩ => true
  | _ => false

/-- The greatest `t ≤ n` at which `p` holds: `range(..=n).next_back()`, searching from `n`
down. -/
def latest (p : Nat → Bool) : Nat → Option Nat
  | 0 => if p 0 then some 0 else none
  | n + 1 => if p (n + 1) then some (n + 1) else latest p n

theorem latest_some {p : Nat → Bool} {n t : Nat} (h : latest p n = some t) :
    t ≤ n ∧ p t = true ∧ ∀ u, t < u → u ≤ n → p u = false := by
  induction n with
  | zero =>
    unfold latest at h
    by_cases hp : p 0 = true
    · simp only [hp, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl 0, hp, fun u hu hu' => absurd hu' (by omega)⟩
    · simp [hp] at h
  | succ n ih =>
    unfold latest at h
    by_cases hp : p (n + 1) = true
    · simp only [hp, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨Nat.le_refl _, hp, fun u hu hu' => absurd hu' (by omega)⟩
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      refine ⟨by omega, h2, fun u hu hu' => ?_⟩
      by_cases hun : u = n + 1
      · subst hun
        simpa using hp
      · exact h3 u hu (by omega)

theorem latest_none {p : Nat → Bool} {n : Nat} (h : latest p n = none) :
    ∀ u, u ≤ n → p u = false := by
  induction n with
  | zero =>
    unfold latest at h
    intro u hu
    have : u = 0 := by omega
    subst this
    by_cases hp : p 0 = true
    · simp [hp] at h
    · simpa using hp
  | succ n ih =>
    unfold latest at h
    intro u hu
    by_cases hp : p (n + 1) = true
    · simp [hp] at h
    · simp only [hp, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hun : u = n + 1
      · subst hun
        simpa using hp
      · exact ih h u (by omega)

/-- A point `k ≤ n` where `p` holds is at or below what the search answers. -/
theorem latest_ge {p : Nat → Bool} {n k : Nat} (hk : k ≤ n) (hp : p k = true) :
    ∃ t, latest p n = some t ∧ k ≤ t := by
  cases h : latest p n with
  | none => exact absurd (latest_none h k hk) (by simp [hp])
  | some t =>
    obtain ⟨_, _, h3⟩ := latest_some h
    refine ⟨t, rfl, ?_⟩
    by_cases hkt : k ≤ t
    · exact hkt
    · exact absurd (h3 k (by omega) hk) (by simp [hp])

/-- Two searches agree when their predicates agree from a point `k` where they hold up to `n`:
the search stops at or above `k`. -/
theorem latest_congr {p q : Nat → Bool} {k n : Nat} (hkn : k ≤ n) (hp : p k = true)
    (hpq : ∀ u, k ≤ u → u ≤ n → p u = q u) : latest p n = latest q n := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0
    unfold latest
    rw [← hpq 0 (Nat.le_refl 0) (Nat.le_refl 0)]
  | succ n ih =>
    unfold latest
    rw [← hpq (n + 1) hkn (Nat.le_refl _)]
    by_cases hpn : p (n + 1) = true
    · simp [hpn]
    · have hkn' : k ≤ n := by
        by_cases hkeq : k = n + 1
        · subst hkeq
          exact absurd hp hpn
        · omega
      simp only [hpn, Bool.false_eq_true, ↓reduceIte]
      exact ih hkn' (fun u hu hu' => hpq u hu (by omega))

/-- A key's records, from `commit_ts` (the `BTreeMap` of `CF_WRITE`). -/
abbrev Writes := Nat → Option Rec

/-- `get_latest_write(key, ts)`: the greatest record at or below `ts`, of any kind. -/
def latestWrite (m : Writes) (ts : Nat) : Option Nat := latest (fun t => (m t).isSome) ts

/-- `get_latest_commit(key, ts)`: the greatest Put or Delete at or below `ts`. -/
def latestCommit (m : Writes) (ts : Nat) : Option Nat := latest (fun t => isCommit (m t)) ts

/-- Prewrite's pass 2 on `get_latest_write(key, u64::MAX)`: a Rollback record or a commit at or
after `start_ts` rejects the key. -/
def prewriteRejects (m : Writes) (top start : Nat) : Bool :=
  match latestWrite m top with
  | some t => decide (start ≤ t)
  | none => false

/-- Checking only the greatest record is checking them all: pass 2 rejects exactly when some
record lies at or after `start_ts`. -/
theorem prewriteRejects_iff {m : Writes} {top start : Nat} :
    prewriteRejects m top start = true ↔ ∃ t, t ≤ top ∧ (m t).isSome = true ∧ start ≤ t := by
  unfold prewriteRejects latestWrite
  constructor
  · intro h
    cases hl : latest (fun t => (m t).isSome) top with
    | none => simp [hl] at h
    | some t =>
      simp only [hl, decide_eq_true_eq] at h
      obtain ⟨h1, h2, _⟩ := latest_some hl
      exact ⟨t, h1, h2, h⟩
  · rintro ⟨t, h1, h2, h3⟩
    obtain ⟨t', hl, ht'⟩ := latest_ge (p := fun t => (m t).isSome) h1 h2
    simp only [hl, decide_eq_true_eq]
    omega

/-- The SSI validation on `get_latest_commit(key, u64::MAX)`: the greatest Put or Delete fails
the key when it is after `start_ts`. -/
def ssiFails (m : Writes) (top start : Nat) : Bool :=
  match latestCommit m top with
  | some t => decide (start < t)
  | none => false

/-- What the validation is for: some transaction committed the key after `start_ts`. -/
def committedAfter (m : Writes) (top start : Nat) : Prop :=
  ∃ t, t ≤ top ∧ isCommit (m t) = true ∧ start < t

theorem isCommit_isSome {r : Option Rec} (h : isCommit r = true) : r.isSome = true := by
  match r, h with
  | some _, _ => rfl

/-- The validation is exact: it fails a key exactly when some transaction committed it after
`start_ts`, whatever Rollback records lie above. -/
theorem ssiFails_exact {m : Writes} {top start : Nat} :
    ssiFails m top start = true ↔ committedAfter m top start := by
  unfold ssiFails latestCommit committedAfter
  constructor
  · intro h
    cases hl : latest (fun t => isCommit (m t)) top with
    | none => simp [hl] at h
    | some t =>
      simp only [hl, decide_eq_true_eq] at h
      obtain ⟨h1, h2, _⟩ := latest_some hl
      exact ⟨t, h1, h2, h⟩
  · rintro ⟨t, h1, h2, h3⟩
    obtain ⟨t', hl, ht'⟩ := latest_ge (p := fun t => isCommit (m t)) h1 h2
    simp only [hl, decide_eq_true_eq]
    omega

/-- The rule before the fix: the validation on `get_latest_write(key, u64::MAX)`, the greatest
record of any kind, failing the key only when that record is a commit after `start_ts`. -/
def ssiFailsRecord (m : Writes) (top start : Nat) : Bool :=
  match latestWrite m top with
  | some t => isCommit (m t) && decide (start < t)
  | none => false

/-- The old rule was exact only while no Rollback record lay after `start_ts`. -/
theorem ssiFailsRecord_exact {m : Writes} {top start : Nat}
    (hno : ∀ t r, start < t → t ≤ top → m t = some r → r.kind ≠ .rb) :
    ssiFailsRecord m top start = true ↔ committedAfter m top start := by
  unfold ssiFailsRecord latestWrite committedAfter
  constructor
  · intro h
    cases hl : latest (fun t => (m t).isSome) top with
    | none => simp [hl] at h
    | some t =>
      simp only [hl, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨h1, _, _⟩ := latest_some hl
      exact ⟨t, h1, h.1, h.2⟩
  · rintro ⟨t, h1, h2, h3⟩
    obtain ⟨t', hl, ht'⟩ := latest_ge (p := fun t => (m t).isSome) h1 (isCommit_isSome h2)
    obtain ⟨h1', h2', _⟩ := latest_some hl
    simp only [hl, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, by omega⟩
    cases hm : m t' with
    | none => simp [hm] at h2'
    | some r =>
      have hk := hno t' r (by omega) h1' hm
      cases r with
      | mk kind st => cases kind <;> simp_all [isCommit]

/-- The masked validation, the TLA+ trace of `ssi_latest_record`'s key: a Serializable
transaction that began at 1 read the key, a second committed it at 3, a third left a Rollback
record at its `start_ts` 5. The key was committed after 1: the old rule passed it, the new one
fails it. -/
def maskedKey : Writes := fun t =>
  if t = 3 then some ⟨.put, 2⟩ else if t = 5 then some ⟨.rb, 5⟩ else none

theorem ssi_masked :
    committedAfter maskedKey 10 1 ∧ ssiFailsRecord maskedKey 10 1 = false
      ∧ ssiFails maskedKey 10 1 = true :=
  ⟨⟨3, by decide, by decide, by decide⟩, by decide, by decide⟩

/-! ## Garbage collection -/

/-- `gc_writes(key, watermark)`: keep the greatest Put or Delete at or below the watermark and
every record above it, drop those below it. -/
def gcWrites (m : Writes) (w : Nat) : Writes :=
  match latestCommit m w with
  | none => m
  | some k => fun t => if t < k then none else m t

/-- Every read at or above the watermark finds the version it found before. -/
theorem gcWrites_keeps_reads {m : Writes} {w ts : Nat} (hts : w ≤ ts) :
    latestCommit (gcWrites m w) ts = latestCommit m ts := by
  unfold gcWrites
  cases hk : latestCommit m w with
  | none => rfl
  | some k =>
    obtain ⟨hkw, hc, _⟩ := latest_some hk
    unfold latestCommit
    symm
    apply latest_congr (k := k) (by omega) hc
    intro u hu _
    simp [show ¬u < k by omega]

/-- Prewrite's check, on the greatest record of any kind at or above the watermark, finds what
it found before: the commit kept is a record, and nothing at or above it goes. -/
theorem gcWrites_keeps_prewrite {m : Writes} {w top : Nat} (htop : w ≤ top) :
    latestWrite (gcWrites m w) top = latestWrite m top := by
  unfold gcWrites
  cases hk : latestCommit m w with
  | none => rfl
  | some k =>
    obtain ⟨hkw, hc, _⟩ := latest_some hk
    unfold latestWrite
    symm
    apply latest_congr (k := k) (by omega) (isCommit_isSome hc)
    intro u hu _
    simp [show ¬u < k by omega]

/-- The rule before the fix: keep the greatest record of any kind at or below the watermark. -/
def gcWritesRecord (m : Writes) (w : Nat) : Writes :=
  match latestWrite m w with
  | none => m
  | some k => fun t => if t < k then none else m t

/-- The TLA+ trace of `gc_keeps_latest_record`'s key: committed at 2, a Rollback record at 4, the
watermark 4. A read at 6 finds the commit at 2; after the old rule's pass it found none, after
the new one's it still finds it. -/
def rolledBackKey : Writes := fun t =>
  if t = 2 then some ⟨.put, 1⟩ else if t = 4 then some ⟨.rb, 4⟩ else none

theorem gcWrites_loses_under_rollback :
    latestCommit rolledBackKey 6 = some 2
      ∧ latestCommit (gcWritesRecord rolledBackKey 4) 6 = none
      ∧ latestCommit (gcWrites rolledBackKey 4) 6 = some 2 :=
  ⟨by decide, by decide, by decide⟩

/-- `gc_data(key, watermark)` on a key's data (`CF_DATA`, from `start_ts`): keep the data the
greatest commit at or below the watermark names, and every version above it; drop those below. -/
def gcData {α : Type} (d : Nat → Option α) (m : Writes) (w : Nat) : Nat → Option α :=
  match latestCommit m w with
  | none => d
  | some c =>
    match m c with
    | some r => fun s => if s < r.start then none else d s
    | none => d

/-- When the key's commits come in the order of their `start_ts`, a read at or above the
watermark still finds the data of the version it finds. -/
theorem gcData_keeps_reads {α : Type} {d : Nat → Option α} {m : Writes} {w ts j : Nat} {rj : Rec}
    (hmono : ∀ c1 c2 r1 r2, c1 ≤ c2 → m c1 = some r1 → m c2 = some r2 →
      isCommit (some r1) = true → isCommit (some r2) = true → r1.start ≤ r2.start)
    (hts : w ≤ ts) (hj : latestCommit m ts = some j) (hmj : m j = some rj) :
    gcData d m w rj.start = d rj.start := by
  cases hc : latestCommit m w with
  | none => simp [gcData, hc]
  | some c =>
    obtain ⟨hcw, hcc, _⟩ := latest_some hc
    obtain ⟨_, hjc, hjmax⟩ := latest_some hj
    have hcj : c ≤ j := by
      by_cases h : c ≤ j
      · exact h
      · exact absurd (hjmax c (by omega) (by omega)) (by simp [hcc])
    cases hmc : m c with
    | none => simp [gcData, hc, hmc]
    | some r =>
      rw [hmc] at hcc
      rw [hmj] at hjc
      have hst : r.start ≤ rj.start := hmono c j r rj hcj hmc hmj hcc hjc
      simp [gcData, hc, hmc, show ¬rj.start < r.start by omega]

/-- The rule before the fix: keep the greatest data version at or below the watermark, a
prewrite's too. -/
def gcDataLatest {α : Type} (d : Nat → Option α) (w : Nat) : Nat → Option α :=
  match latest (fun s => (d s).isSome) w with
  | none => d
  | some k => fun s => if s < k then none else d s

/-- The TLA+ trace of `gc_keeps_latest_data`'s key: the setup transaction's data at `start_ts` 1
(committed at 2), a prewrite's at 3 not committed, the watermark 3. A read at 4 finds the commit
at 2, which names `start_ts` 1: the old rule's pass dropped that data, the new one's keeps it. -/
def seedData : Nat → Option Nat := fun s => if s = 1 then some 0 else if s = 3 then some 1 else none

def seedWrites : Writes := fun t => if t = 2 then some ⟨.put, 1⟩ else none

theorem gcData_loses_under_prewrite :
    latestCommit seedWrites 4 = some 2 ∧ seedData 1 = some 0 ∧ gcDataLatest seedData 3 1 = none
      ∧ gcData seedData seedWrites 3 1 = some 0 :=
  ⟨by decide, by decide, by decide, by decide⟩

end Kovan.Mvcc
