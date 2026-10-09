module

public import ArithLemmas.Mathlib.Nat.CeilSqrt
public import ArithLemmas.Mathlib.Nat.BitLength
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith

/-!
# 切り上げ平方根と対数の最小性・境界条件

`ceilSqrt n` は `n ≤ k²` を満たす最小の自然数 `k` である。
同様に、任意の基数 `B > 1` について、`Nat.clog B n` は
`n ≤ B^k` を満たす最小の指数 `k` である。
以下では片側の不等式だけでなく、値を確定するための
必要十分条件および境界の特徴付けを証明する。
-/

public section

namespace ArithLemmas.Mathlib.Nat

open ArithLemmas.Mathlib.Defs.Nat

/-- **切り上げ平方根の正確な最小性。**
`n ≤ k²` が成立することと `ceilSqrt n ≤ k` は同値である。 -/
theorem ceilSqrt_le_iff_sq_le (n k : ℕ) :
    ceilSqrt n ≤ k ↔ n ≤ k ^ 2 := by
  constructor
  · intro hk
    exact (self_le_ceilSqrt_sq n).trans (Nat.pow_le_pow_left hk 2)
  · intro hk
    by_cases hs : (Nat.sqrt n) ^ 2 = n
    · rw [ceilSqrt_eq_sqrt_of_square n hs]
      by_contra hh
      have hlt : k < Nat.sqrt n := Nat.lt_of_not_ge hh
      have hsq : (k + 1) ^ 2 ≤ (Nat.sqrt n) ^ 2 :=
        Nat.pow_le_pow_left (Nat.succ_le_of_lt hlt) 2
      nlinarith
    · rw [ceilSqrt_eq_sqrt_add_one_of_not_square n hs]
      by_contra hh
      have hle : k ≤ Nat.sqrt n := by omega
      have hsq : k ^ 2 ≤ (Nat.sqrt n) ^ 2 :=
        Nat.pow_le_pow_left hle 2
      have hbound : (Nat.sqrt n) ^ 2 < n :=
        lt_of_le_of_ne (Nat.sqrt_le' n) hs
      omega

/-- 切り上げ平方根の二乗は、必ず元の自然数以上となる。
また、この性質を持つ自然数のうち切り上げ平方根が最小である。 -/
theorem ceilSqrt_minimal_square (n : ℕ) :
    n ≤ (ceilSqrt n) ^ 2 ∧
      ∀ k : ℕ, n ≤ k ^ 2 → ceilSqrt n ≤ k := by
  exact ⟨self_le_ceilSqrt_sq n,
    fun k hk => (ceilSqrt_le_iff_sq_le n k).mpr hk⟩

/-- 切り上げ平方根の値を、平方の上界とそれ未満の数の不適合性で
正確に特徴付ける。 -/
theorem ceilSqrt_eq_iff (n k : ℕ) :
    ceilSqrt n = k ↔
      n ≤ k ^ 2 ∧ ∀ j : ℕ, j < k → j ^ 2 < n := by
  constructor
  · intro h
    constructor
    · exact (ceilSqrt_le_iff_sq_le n k).mp (le_of_eq h)
    · intro j hj
      by_contra hbad
      have hnj : n ≤ j ^ 2 := Nat.le_of_not_gt hbad
      have hj' := (ceilSqrt_le_iff_sq_le n j).mpr hnj
      omega
  · rintro ⟨hk, hbelow⟩
    apply Nat.le_antisymm
    · exact (ceilSqrt_le_iff_sq_le n k).mpr hk
    · by_contra hbad
      have hlt : ceilSqrt n < k := Nat.lt_of_not_ge hbad
      have hsq := hbelow (ceilSqrt n) hlt
      exact (not_le_of_gt hsq) (self_le_ceilSqrt_sq n)

/-- **任意の基数 `B > 1` に対する切り上げ対数の正確な最小性。** -/
theorem clog_le_iff_pow_le (B n k : ℕ) (hB : 1 < B) :
    Nat.clog B n ≤ k ↔ n ≤ B ^ k :=
  Nat.clog_le_iff_le_pow hB

/-- 切り上げ対数は、冪が与えられた自然数以上となる最小の指数である。 -/
theorem clog_minimal_pow (B n : ℕ) (hB : 1 < B) :
    n ≤ B ^ (Nat.clog B n) ∧
      ∀ k : ℕ, n ≤ B ^ k → Nat.clog B n ≤ k := by
  exact ⟨(Nat.clog_le_iff_le_pow hB).mp le_rfl,
    fun k hk => (Nat.clog_le_iff_le_pow hB).mpr hk⟩

/-- 切り上げ対数の値を境界条件で完全に特徴付ける。
`n = 0` や `k = 0` の場合も含む。 -/
theorem clog_eq_iff (B n k : ℕ) (hB : 1 < B) :
    Nat.clog B n = k ↔
      n ≤ B ^ k ∧ ∀ j : ℕ, j < k → B ^ j < n := by
  constructor
  · intro h
    constructor
    · exact (Nat.clog_le_iff_le_pow hB).mp (le_of_eq h)
    · intro j hj
      exact (Nat.lt_clog_iff_pow_lt hB).mp (h.symm ▸ hj)
  · rintro ⟨hupper, hlower⟩
    apply Nat.le_antisymm
    · exact (Nat.clog_le_iff_le_pow hB).mpr hupper
    · by_contra hbad
      have hj : Nat.clog B n < k := Nat.lt_of_not_ge hbad
      have hlt := hlower (Nat.clog B n) hj
      have hle := (Nat.clog_le_iff_le_pow hB).mp (le_refl (Nat.clog B n))
      omega


/-- 切り捨て対数について、対応する冪の区間による正確な特徴付け。 -/
theorem log_eq_iff_pow_interval (B n k : ℕ)
    (hB : 1 < B) (hn : 0 < n) :
    Nat.log B n = k ↔ B ^ k ≤ n ∧ n < B ^ (k + 1) := by
  exact Nat.log_eq_iff (Or.inr ⟨hB, hn.ne'⟩)

end ArithLemmas.Mathlib.Nat
