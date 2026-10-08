module

public import ArithLemmas.Mathlib.Nat.CeilSqrt
public import ArithLemmas.Mathlib.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

/-!
# 切り上げ平方根と実数平方根の橋渡し（第4段階4A）

自然数の切り上げ平方根を実数に埋め込み、通常の `Real.sqrt` との
比較・上界・下界を示す。
原典：OpenAI `OAI/Algebra/DepthFive/CeilArithmetic.lean`。
-/

public section

namespace ArithLemmas.Mathlib.Real

open ArithLemmas.Mathlib.Defs.Nat

/-- 自然数の切り上げ平方根は、実数平方根より高々１だけ大きい。 -/
theorem ceilSqrt_cast_le_real_sqrt_add_one (n : ℕ) :
    (ceilSqrt n : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := by
  have hnat : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' n
  have hceil : (ceilSqrt n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
    exact_mod_cast ArithLemmas.Mathlib.Nat.ceilSqrt_le_sqrt_add_one n
  linarith

/-- 実数平方根は自然数の切り上げ平方根以下である。 -/
theorem real_sqrt_le_ceilSqrt_cast (n : ℕ) :
    Real.sqrt (n : ℝ) ≤ (ceilSqrt n : ℝ) := by
  apply (Real.sqrt_le_left (Nat.cast_nonneg _)).mpr
  exact_mod_cast ArithLemmas.Mathlib.Nat.self_le_ceilSqrt_sq n

/-- 自然数の切り上げ平方根を実数に埋め込むと、平方根を幅１の区間に挟める。 -/
theorem real_sqrt_ceilSqrt_bounds (n : ℕ) :
    Real.sqrt (n : ℝ) ≤ (ceilSqrt n : ℝ) ∧
      (ceilSqrt n : ℝ) ≤ Real.sqrt (n : ℝ) + 1 :=
  ⟨real_sqrt_le_ceilSqrt_cast n, ceilSqrt_cast_le_real_sqrt_add_one n⟩

end ArithLemmas.Mathlib.Real
