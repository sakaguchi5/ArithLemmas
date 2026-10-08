module

public import ArithLemmas.Pure.Nat.GCD
public import ArithLemmas.Pure.Int.Parts
public import ArithLemmas.Pure.Binary.SignedDivision
public import ArithLemmas.Mathlib.Rat.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Pure算術から有理数への橋渡し（第3段階3D）

GCDでの縮約が有理数値を保存すること、整数の正負分解、
符号付き二進除算の復元式を有理数へ移す。
-/

public section

namespace ArithLemmas.Mathlib.Rat

open ArithLemmas.Pure.Defs.Nat
open ArithLemmas.Pure.Defs.Int
open ArithLemmas.Pure.Defs.Binary

/-- 分母が正なら、GCDで両項を縮約しても有理数は変化しない。 -/
theorem gcd_ratio_eq_reduced (a u : Nat) (hu : 0 < u) :
    (a : ℚ) / (u : ℚ) =
      ((a / Nat.gcd a u : Nat) : ℚ) / ((u / Nat.gcd a u : Nat) : ℚ) := by
  have ha : Nat.gcd a u * (a / Nat.gcd a u) = a := by
    simpa only [gcdCoordinates] using
      ArithLemmas.Pure.Nat.gcdCoordinates_recover_left (a, u)
  have hden : Nat.gcd a u * (u / Nat.gcd a u) = u := by
    simpa only [gcdCoordinates] using
      ArithLemmas.Pure.Nat.gcdCoordinates_recover_right (a, u)
  have haq : (Nat.gcd a u : ℚ) * ((a / Nat.gcd a u : Nat) : ℚ) = (a : ℚ) := by
    exact_mod_cast ha
  have hdenq : (Nat.gcd a u : ℚ) * ((u / Nat.gcd a u : Nat) : ℚ) = (u : ℚ) := by
    exact_mod_cast hden
  have hg : (0 : ℚ) < (Nat.gcd a u : ℚ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_right a hu
  have hy : (0 : ℚ) < ((u / Nat.gcd a u : Nat) : ℚ) := by
    exact_mod_cast ArithLemmas.Pure.Nat.reduced_modulus_pos a u hu
  rw [← haq, ← hdenq]
  field_simp [ne_of_gt hg, ne_of_gt hy]

/-- 自然数を有理数に埋め込んだ商は常に非負である。
分母がゼロの場合も、有理数の除算の規約により成立する。 -/
theorem nat_ratio_nonneg (a u : Nat) :
    (0 : ℚ) ≤ (a : ℚ) / (u : ℚ) := by
  positivity

/-- 分子が分母以下なら、その比は１以下である。 -/
theorem nat_ratio_le_one (a u : Nat) (hu : 0 < u) (hau : a ≤ u) :
    (a : ℚ) / (u : ℚ) ≤ 1 := by
  have huq : (0 : ℚ) < (u : ℚ) := by exact_mod_cast hu
  have hle : (a : ℚ) ≤ (u : ℚ) := by exact_mod_cast hau
  exact (div_le_iff₀ huq).2 (by simpa using hle)

/-- GCD縮約済みの比にも同じ１以下の上界が成り立つ。 -/
theorem gcd_reduced_ratio_le_one (a u : Nat) (hu : 0 < u) (hau : a ≤ u) :
    ((a / Nat.gcd a u : Nat) : ℚ) / ((u / Nat.gcd a u : Nat) : ℚ) ≤ 1 := by
  rw [← gcd_ratio_eq_reduced a u hu]
  exact nat_ratio_le_one a u hu hau

/-- 整数の正負部分による分解は、有理数に埋め込んでも成立する。 -/
theorem int_parts_decompose_rat (z : Int) :
    ((positivePart z : Nat) : ℚ) - ((negativePart z : Nat) : ℚ) = (z : ℚ) := by
  exact_mod_cast ArithLemmas.Pure.Int.int_decompose z

/-- 符号付き二進除算の商と余りの恒等式は、有理数上にも成立する。 -/
theorem signed_division_recover_rat (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    (signedBitsValue negative xs : ℚ) =
      (bitsValue divisor : ℚ) *
        (signedBitsValue negative (divideSignedBits negative divisor xs).1 : ℚ) +
        (bitsValue (divideSignedBits negative divisor xs).2 : ℚ) := by
  exact_mod_cast ArithLemmas.Pure.Binary.divideSignedBits_recover negative divisor xs hd

/-- 符号付き二進除算の余りの上界は、有理数でも保存される。 -/
theorem signed_division_remainder_lt_rat (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    (bitsValue (divideSignedBits negative divisor xs).2 : ℚ) <
      (bitsValue divisor : ℚ) := by
  exact_mod_cast ArithLemmas.Pure.Binary.divideSignedBits_remainder_lt negative divisor xs hd

end ArithLemmas.Mathlib.Rat
