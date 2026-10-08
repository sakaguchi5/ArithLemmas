import Mathlib.Tactic.Ring

/-!
# 有理数の四則演算

分母を共有する分数の加減算など、計算の際に再利用できる恒等式。
-/
set_option linter.style.docString false

namespace ArithLemmas.Mathlib.Rat

/-- 分母が等しい二つの分数の和を、一つの分数にまとめられる。-/
theorem add_same_denominator (a b d : ℚ) :
    a / d + b / d = (a + b) / d := by
  ring

/-- 分母が等しい二つの分数の差を、一つの分数にまとめられる。-/
theorem sub_same_denominator (a b d : ℚ) :
    a / d - b / d = (a - b) / d := by
  ring

/-- 二つの有理数の平方の差は、和と差の積に等しい。-/
theorem difference_of_squares (a b : ℚ) :
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  ring

end ArithLemmas.Mathlib.Rat
