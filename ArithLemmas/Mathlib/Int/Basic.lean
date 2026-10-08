import ArithLemmas.Tactic.Int.Basic
import Mathlib.Data.Int.Notation
import Mathlib.Algebra.Order.Ring.Abs

/-!
# 整数の差と距離

絶対値から得られる基本的な距離の性質を整理する。
-/
set_option linter.style.docString false

namespace ArithLemmas.Mathlib.Int

/-- 二つの整数の差の絶対値は、差を取る順序に依存しない。-/
theorem abs_sub_symm (a b : ℤ) : |a - b| = |b - a| :=
  abs_sub_comm a b

/-- 三つの整数の間の距離は、途中の点を経由する距離の和以下である。-/
theorem abs_sub_triangle (a b c : ℤ) :
    |a - c| ≤ |a - b| + |b - c| := by
  calc
    |a - c| = |(a - b) + (b - c)| := by congr 1
                                        omega
    _ ≤ |a - b| + |b - c| := abs_add_le _ _

/-- 等しい整数の差の絶対値は０である。-/
theorem abs_sub_eq_zero_of_eq {a b : ℤ} (h : a = b) : |a - b| = 0 := by
  subst b
  simp

end ArithLemmas.Mathlib.Int
