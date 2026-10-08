module

public import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring

/-!
# 可換半環上の恒等式

自然数・整数・有理数などに共通する多項式恒等式を、
可換半環という一般的な設定で証明する。
-/
set_option linter.style.docString false

public section

namespace ArithLemmas.Mathlib.Algebra

/-- 可換半環では和の平方を分配法則で展開できる。-/
theorem add_sq {R : Type*} [CommSemiring R] (a b : R) :
    (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- 可換環では平方の差を二つの一次式の積に分解できる。-/
theorem sub_sq {R : Type*} [CommRing R] (a b : R) :
    a ^ 2 - b ^ 2 = (a - b) * (a + b) := by
  ring

/-- 可換半環では三つの数の積は括り方に依存しない。-/
theorem reassociate_product {R : Type*} [CommSemiring R] (a b c : R) :
    a * (b * c) = c * (a * b) := by
  ring

end ArithLemmas.Mathlib.Algebra
