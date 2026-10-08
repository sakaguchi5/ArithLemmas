module

public import ArithLemmas.Mathlib.Nat.PrimeGCDProducts
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# 有限素因数集合の対数評価（第4段階4E-1）

自然数の素因数ヒット数を、冪による上界から実数の対数上界へ変換する。
原典：OpenAI `OAI/NumberTheory/EgyptianFractions/PrimeHits.lean`
固定原典：`adc7f1241b42e322a6451854ab7e4b4c146bf78a`
v1.8 ID：85。
-/

public section

namespace ArithLemmas.Mathlib.Real

/-- 大きさ `L > 1` 以上の相異なる素数で法 `u > 0` を割り切るものの個数は、
`log u / log L` 以下となる。原典ID 85。 -/
theorem prime_divisor_population_log_le (P : Finset ℕ) (u L : ℕ)
    (hu : 0 < u) (hL1 : 1 < L)
    (hp : ∀ p ∈ P, p.Prime) (hL : ∀ p ∈ P, L ≤ p) :
    ((P.filter (fun p => p ∣ u)).card : ℝ) ≤
      Real.log (u : ℝ) / Real.log (L : ℝ) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpow := ArithLemmas.Mathlib.Nat.prime_divisor_population_pow_le P u L hu hp hL
  have hreal : (L : ℝ) ^ (P.filter (fun p => p ∣ u)).card ≤ u := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log (pow_pos hLpos _) hreal
  rw [Real.log_pow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by exact_mod_cast hL1))).mpr hlog

end ArithLemmas.Mathlib.Real
