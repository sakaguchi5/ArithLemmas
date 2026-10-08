module

public import ArithLemmas.Pure.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# 自然数に対する数学ライブラリ上の定理

整除、最大公約数、最小公倍数に関する問題非依存の定理を集める。
原典由来の証明を採用する場合は、名称と内容の対応を残す。
-/
set_option linter.style.docString false

public section

namespace ArithLemmas.Mathlib.Nat

open ArithLemmas.Pure.Defs.Nat

/-- 二つの整数が同じ数を割り切るなら、
一方を両者の最大公約数で割った数は、指定した商を割り切る。
原典：切り詰めた約数の評価。-/
theorem div_gcd_dvd_quotient {a d n : ℕ} (ha : a ∣ n) (hd : d ∣ n) :
    a / Nat.gcd a d ∣ n / d := by
  apply (Nat.dvd_div_iff_mul_dvd hd).2
  have hlcm : Nat.lcm a d = d * (a / Nat.gcd a d) := by
    rw [Nat.lcm_eq_mul_div, Nat.mul_comm a d,
      Nat.mul_div_assoc d (Nat.gcd_dvd_left a d)]
  rw [← hlcm]
  exact Nat.lcm_dvd ha hd

/-- 最大公約数と、その最大公約数で割った商との組から、元の自然数を復元できる。
原典：切り詰めた約数の評価。-/
theorem gcdSplit_recover (a d : ℕ) :
    (gcdSplit a d).2 * (gcdSplit a d).1 = a := by
  simp only [gcdSplit]
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left a d)

/-- 最大公約数と商の組による写像は単射である。
原典：切り詰めた約数の評価。-/
theorem gcd_split_injective (d : ℕ) :
    Function.Injective (fun a : ℕ => gcdSplit a d) := by
  intro a b hab
  have h := congrArg (fun z : ℕ × ℕ => z.2 * z.1) hab
  calc
    a = (gcdSplit a d).2 * (gcdSplit a d).1 := (gcdSplit_recover a d).symm
    _ = (gcdSplit b d).2 * (gcdSplit b d).1 := h
    _ = b := gcdSplit_recover b d

/-- 三つの自然数の最大公約数を順に取っても、
最後の２変数の最大公約数を超えない。
原典：ヤコブスタール問題における剰余の評価。-/
theorem gcd_three_le_second (N x y : ℕ) (hN : 0 < N) :
    Nat.gcd N (Nat.gcd x y) ≤ Nat.gcd y N := by
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right y hN)
  exact Nat.dvd_gcd
    ((Nat.gcd_dvd_right N (Nat.gcd x y)).trans (Nat.gcd_dvd_right x y))
    (Nat.gcd_dvd_left N (Nat.gcd x y))

end ArithLemmas.Mathlib.Nat
