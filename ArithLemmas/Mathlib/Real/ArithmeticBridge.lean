module

public import ArithLemmas.Pure.Nat.GCD
public import ArithLemmas.Pure.Int.Parts
public import ArithLemmas.Pure.Binary.SignedDivision
public import ArithLemmas.Mathlib.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Pure算術から実数への橋渡し（第3段階3D）

GCD座標・二進算術・整数正負分解の恒等式と大小関係を実数へ持ち上げる。
-/

public section

namespace ArithLemmas.Mathlib.Real

open ArithLemmas.Pure.Defs.Nat
open ArithLemmas.Pure.Defs.Int
open ArithLemmas.Pure.Defs.Binary

/-- GCD座標の第一入力復元式は実数に埋め込んでも成立する。 -/
theorem gcdCoordinates_recover_left_real (v : Nat × Nat) :
    ((gcdCoordinates v).1 : ℝ) * ((gcdCoordinates v).2.1 : ℝ) = (v.1 : ℝ) := by
  exact_mod_cast ArithLemmas.Pure.Nat.gcdCoordinates_recover_left v

/-- GCD座標の第二入力復元式も実数に埋め込んで成立する。 -/
theorem gcdCoordinates_recover_right_real (v : Nat × Nat) :
    ((gcdCoordinates v).1 : ℝ) * ((gcdCoordinates v).2.2 : ℝ) = (v.2 : ℝ) := by
  exact_mod_cast ArithLemmas.Pure.Nat.gcdCoordinates_recover_right v

/-- 二進列の実数値は、桁数に対応する２の冪未満である。 -/
theorem bitsValue_lt_two_pow_real (xs : List Bool) :
    (bitsValue xs : ℝ) < (2 : ℝ) ^ xs.length := by
  exact_mod_cast ArithLemmas.Pure.Binary.bitsValue_lt_two_pow_length xs

/-- 整数の正負部分による分解は実数に埋め込んでも保存される。 -/
theorem int_parts_decompose_real (z : Int) :
    ((positivePart z : Nat) : ℝ) - ((negativePart z : Nat) : ℝ) = (z : ℝ) := by
  exact_mod_cast ArithLemmas.Pure.Int.int_decompose z

/-- 符号付き二進除算の復元式を実数に埋め込む。 -/
theorem signed_division_recover_real (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    (signedBitsValue negative xs : ℝ) =
      (bitsValue divisor : ℝ) *
        (signedBitsValue negative (divideSignedBits negative divisor xs).1 : ℝ) +
        (bitsValue (divideSignedBits negative divisor xs).2 : ℝ) := by
  exact_mod_cast ArithLemmas.Pure.Binary.divideSignedBits_recover negative divisor xs hd

/-- 符号付き二進除算の余りの上界も実数上で成り立つ。 -/
theorem signed_division_remainder_lt_real (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    (bitsValue (divideSignedBits negative divisor xs).2 : ℝ) <
      (bitsValue divisor : ℝ) := by
  exact_mod_cast ArithLemmas.Pure.Binary.divideSignedBits_remainder_lt negative divisor xs hd

/-- 自然数の縮約商は、実数へ埋め込んでも元の自然数以下である。 -/
theorem gcdCoordinates_left_quotient_le_real (v : Nat × Nat) :
    ((gcdCoordinates v).2.1 : ℝ) ≤ (v.1 : ℝ) := by
  exact_mod_cast ArithLemmas.Pure.Nat.gcdCoordinates_left_quotient_le v

end ArithLemmas.Mathlib.Real
