module

public import ArithLemmas.Mathlib.Nat.PrimePowers
public import ArithLemmas.Mathlib.Nat.PrimeGCDProducts
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# 最大公約数と最小公倍数の素因数指数に関する正確な公式

各素数の指数について、最大公約数では二つの指数の最小値、
最小公倍数では最大値を取ることを証明する。
さらに、これらの等式を素数冪の整除性に関する必要十分条件へ接続し、
既存の有限素数積に対する上界評価を正確な等式によって補強する。
-/

public section

namespace ArithLemmas.Mathlib.Nat

/-- 非零の二数の最大公約数における素因数指数は、各指数の最小値に等しい。 -/
theorem gcd_factorization_eq_min (a b p : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.gcd a b).factorization p =
      min (a.factorization p) (b.factorization p) := by
  rw [Nat.factorization_gcd ha hb, Finsupp.inf_apply]

/-- 非零の二数の最小公倍数における素因数指数は、各指数の最大値に等しい。 -/
theorem lcm_factorization_eq_max (a b p : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).factorization p =
      max (a.factorization p) (b.factorization p) := by
  rw [Nat.factorization_lcm ha hb, Finsupp.sup_apply]

/-- 素数冪が最大公約数を割り切る条件を、指数の最小値で特徴付ける。 -/
theorem prime_pow_dvd_gcd_iff_min {a b p k : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    p ^ k ∣ Nat.gcd a b ↔
      k ≤ min (a.factorization p) (b.factorization p) := by
  have hg : Nat.gcd a b ≠ 0 :=
    (Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)).ne'
  rw [prime_pow_dvd_iff_factorization hp hg,
    gcd_factorization_eq_min a b p ha hb]

/-- 素数冪が最小公倍数を割り切る条件を、指数の最大値で特徴付ける。 -/
theorem prime_pow_dvd_lcm_iff_max {a b p k : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    p ^ k ∣ Nat.lcm a b ↔
      k ≤ max (a.factorization p) (b.factorization p) := by
  have hl : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  rw [prime_pow_dvd_iff_factorization hp hl,
    lcm_factorization_eq_max a b p ha hb]

/-- `p^k` が最大公約数を割り切ることと、元の二数をともに割り切ることは同値。 -/
theorem prime_pow_dvd_gcd_iff_both {a b p k : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    p ^ k ∣ Nat.gcd a b ↔ p ^ k ∣ a ∧ p ^ k ∣ b := by
  rw [prime_pow_dvd_gcd_iff_min hp ha hb,
    le_min_iff,
    ← prime_pow_dvd_iff_factorization hp ha,
    ← prime_pow_dvd_iff_factorization hp hb]

/-- `p^k` が最小公倍数を割り切ることと、元の二数の少なくとも一方を
割り切ることは同値である。 -/
theorem prime_pow_dvd_lcm_iff_either {a b p k : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0) :
    p ^ k ∣ Nat.lcm a b ↔ p ^ k ∣ a ∨ p ^ k ∣ b := by
  rw [prime_pow_dvd_lcm_iff_max hp ha hb,
    le_max_iff,
    ← prime_pow_dvd_iff_factorization hp ha,
    ← prime_pow_dvd_iff_factorization hp hb]

end ArithLemmas.Mathlib.Nat
