module

public import ArithLemmas.Pure.Nat.Basic

/-!
# 自然数除算・切り上げ除算の導出定理

既存の Pure `ceilDiv` と Lean 本体の自然数除算の規則を再利用する。
原典：Computability/WLIdentification/PolynomialArithmetic (`div_cap`)。
-/

public section

namespace ArithLemmas.Pure.Nat

open ArithLemmas.Pure.Defs.Nat

/-- 分母を `min y (x + 1)` で切り詰めても自然数の商は変わらない。
`y = 0` の場合も Lean の自然数除算の規約の下で成り立つ。 -/
theorem div_cap (x y : Nat) : x / min y (x + 1) = x / y := by
  by_cases hy : y ≤ x + 1
  · rw [Nat.min_eq_left hy]
  · rw [Nat.min_eq_right (by omega), Nat.div_eq_of_lt (by omega),
      Nat.div_eq_of_lt (by omega)]

/-- 分母が被除数の次の自然数以下なら、切り詰め操作は何も変えない。 -/
theorem div_cap_small (x y : Nat) (hy : y ≤ x + 1) :
    min y (x + 1) = y := Nat.min_eq_left hy

/-- 被除数より大きい分母に対する商はゼロである。 -/
theorem div_zero_of_gt (x y : Nat) (hy : x < y) : x / y = 0 :=
  Nat.div_eq_of_lt hy

/-- 正の除数による切り上げ除算は、正の分子に対して正である。 -/
theorem ceilDiv_pos {n t : Nat} (hn : 0 < n) (ht : 0 < t) :
    0 < ceilDiv n t := by
  unfold ceilDiv
  apply Nat.div_pos
  · omega
  · omega

/-- 切り上げ除算に除数を掛けた値は、既存の除算上界で抑えられる。 -/
theorem ceilDiv_scaled_bound (n t : Nat) :
    ceilDiv n t * t ≤ n + t - 1 :=
  ceilDiv_mul_le n t

end ArithLemmas.Pure.Nat
