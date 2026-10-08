import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 実数の初等的不等式

整数・有理数から実数へ移した評価にも使用できる基本補題。
-/
set_option linter.style.docString false

namespace ArithLemmas.Mathlib.Real

/-- 二つの実数の差の絶対値は、それぞれの絶対値の和以下である。-/
theorem abs_sub_le_sum (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  calc
    |a - b| = |a + (-b)| := by simp only [sub_eq_add_neg]
    _ ≤ |a| + |-b| := abs_add_le _ _
    _ = |a| + |b| := by simp

/-- 二つの実数の積の２倍は、平方の和以下である。-/
theorem twice_mul_le_sq_add_sq (a b : ℝ) :
    2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- 二つの実数の和の平方を展開する。-/
theorem add_sq_expansion (a b : ℝ) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

end ArithLemmas.Mathlib.Real
