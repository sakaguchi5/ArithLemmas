module

public import ArithLemmas.Mathlib.Defs.Nat.CeilSqrt
public import ArithLemmas.Pure.Nat.Basic
/-!
# 自然数の切り上げ平方根：導出定理（第4段階4A）

`ceilSqrt` の基本性質、平方上界と、Pure層の `ceilDiv` との関係を示す。
OpenAIの `OAI/Algebra/DepthFive/CeilArithmetic.lean` を独立算術APIへ整理。
Lean本体に依存する Pure 層は変更しない。
-/

public section

namespace ArithLemmas.Mathlib.Nat

open ArithLemmas.Mathlib.Defs.Nat
open ArithLemmas.Pure.Defs.Nat

/-- ０の切り上げ平方根は０である。 -/
@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by
  simp [ceilSqrt]

/-- １の切り上げ平方根は１である。 -/
@[simp] theorem ceilSqrt_one : ceilSqrt 1 = 1 := by
  simp [ceilSqrt]

/-- ２の切り上げ平方根は２である。 -/
@[simp] theorem ceilSqrt_two : ceilSqrt 2 = 2 := by
  simp [ceilSqrt, Nat.sqrt_two]

/-- 通常の整数平方根は、その切り上げ以下である。 -/
theorem sqrt_le_ceilSqrt (n : ℕ) : Nat.sqrt n ≤ ceilSqrt n := by
  unfold ceilSqrt
  omega

/-- 平方根の切り上げは、整数平方根に１を加えた値以下である。 -/
theorem ceilSqrt_le_sqrt_add_one (n : ℕ) :
    ceilSqrt n ≤ Nat.sqrt n + 1 := by
  unfold ceilSqrt
  split <;> omega

/-- 完全平方数の場合、切り上げ平方根と整数平方根は一致する。 -/
theorem ceilSqrt_eq_sqrt_of_square (n : ℕ)
    (h : (Nat.sqrt n) ^ 2 = n) : ceilSqrt n = Nat.sqrt n := by
  simp [ceilSqrt, h]

/-- 完全平方数でない場合、切り上げ平方根は整数平方根より１大きい。 -/
theorem ceilSqrt_eq_sqrt_add_one_of_not_square (n : ℕ)
    (h : (Nat.sqrt n) ^ 2 ≠ n) : ceilSqrt n = Nat.sqrt n + 1 := by
  simp [ceilSqrt, h]

/-- 切り上げ平方根を２乗すると元の自然数以上になる。 -/
theorem self_le_ceilSqrt_sq (n : ℕ) :
    n ≤ ceilSqrt n ^ 2 := by
  unfold ceilSqrt
  split
  · rename_i h
    simp [h]
  · have h := Nat.lt_succ_sqrt' n
    simp only [Nat.succ_eq_add_one] at h ⊢
    omega

/-- 正の自然数では切り上げ平方根も正である。 -/
theorem ceilSqrt_pos {n : ℕ} (hn : 0 < n) : 0 < ceilSqrt n :=
  lt_of_lt_of_le (Nat.sqrt_pos.mpr hn) (sqrt_le_ceilSqrt n)

/-- 切り上げ平方根は元の数を超えない。 -/
theorem ceilSqrt_le_self (n : ℕ) : ceilSqrt n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases h : n = 1
  · subst n
    simp
  have hn' : 1 < n := by omega
  have h₁ := ceilSqrt_le_sqrt_add_one n
  have h₂ := Nat.sqrt_lt_self hn'
  omega

/-- `n ≥ 2` なら切り上げ平方根も２以上である。 -/
theorem two_le_ceilSqrt {n : ℕ} (hn : 2 ≤ n) : 2 ≤ ceilSqrt n := by
  have h := self_le_ceilSqrt_sq n
  by_contra hh
  have hh' : ceilSqrt n ≤ 1 := by omega
  have : ceilSqrt n ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left hh' 2
  omega

/-- 正の除数 `t` によるPureの切り上げ除算は、積による上界と同値。 -/
theorem ceilDiv_le_iff {n t r : ℕ} (ht : 0 < t) :
    ceilDiv n t ≤ r ↔ n ≤ r * t := by
  unfold ceilDiv
  rw [Nat.div_le_iff_le_mul_add_pred ht]
  rw [Nat.mul_comm t r]
  omega

/-- 正の除数で切り上げた商と除数の積は分子以上。 -/
theorem self_le_ceilDiv_mul (n : ℕ) {t : ℕ} (ht : 0 < t) :
    n ≤ ceilDiv n t * t :=
  (ceilDiv_le_iff ht).mp le_rfl

/-- 正の除数で切り上げた商は元の自然数以下。 -/
theorem ceilDiv_le_self (n : ℕ) {t : ℕ} (ht : 0 < t) :
    ceilDiv n t ≤ n := by
  apply (ceilDiv_le_iff ht).mpr
  exact Nat.le_mul_of_pos_right n ht

/-- 自然数をその切り上げ平方根で切り上げ除算した値は、その平方根以下。 -/
theorem ceilDiv_ceilSqrt_le (n : ℕ) :
    ceilDiv n (ceilSqrt n) ≤ ceilSqrt n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ceilDiv]
  apply (ceilDiv_le_iff (ceilSqrt_pos hn)).mpr
  simpa [Nat.pow_two] using self_le_ceilSqrt_sq n

end ArithLemmas.Mathlib.Nat
