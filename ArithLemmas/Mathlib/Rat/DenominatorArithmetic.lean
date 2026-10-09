module

public import ArithLemmas.Mathlib.Rat.ArithmeticBridge
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# 有理数分母の整除性：Mathlib の最小共通分母原理からの導出

有限和の分母については `Finset.Rat.den_sum_dvd_lcm_den` と
`Finset.lcm_dvd_iff` が本質的な一般定理である。
個々の分母の「積」を共通分母とする独自定義は廃止する。
一方、有限積の分母の上界には分母の積が必要であり、
その正確な既存定理 `Finset.Rat.den_prod_dvd_prod_den` を直接利用する。
同一の Mathlib 定理の単純な改名は置かず、一般定理の実質的な系のみ残す。
-/

public section

namespace ArithLemmas.Mathlib.Rat

/-- 各既約分母が一つの数を割れば、有理数の有限和の分母もそれを割る。 -/
theorem den_sum_dvd_of_forall {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (D : ℕ)
    (h : ∀ i ∈ s, (f i).den ∣ D) :
    (∑ i ∈ s, f i).den ∣ D :=
  (Finset.Rat.den_sum_dvd_lcm_den s f).trans
    ((Finset.lcm_dvd_iff).2 h)

/-- 二数の分母に共通する倍数は和の分母の倍数でもある。 -/
theorem den_add_dvd_common {a b : ℚ} {D : ℕ}
    (ha : a.den ∣ D) (hb : b.den ∣ D) :
    (a + b).den ∣ D :=
  (Rat.add_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

/-- 二数の分母に共通する倍数は差の分母の倍数でもある。 -/
theorem den_sub_dvd_common {a b : ℚ} {D : ℕ}
    (ha : a.den ∣ D) (hb : b.den ∣ D) :
    (a - b).den ∣ D :=
  (Rat.sub_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

/-- 積の分母は個々の分母の倍数の積を割り切る。 -/
theorem den_mul_dvd_common {a b : ℚ} {A B : ℕ}
    (ha : a.den ∣ A) (hb : b.den ∣ B) :
    (a * b).den ∣ A * B :=
  (Rat.mul_den_dvd a b).trans (Nat.mul_dvd_mul ha hb)

/-- 自然数を掛けても分母に新しい素因数は生じない。 -/
theorem den_mul_nat_dvd_self (a : ℚ) (n : ℕ) :
    (a * (n : ℚ)).den ∣ a.den := by
  simpa only [Rat.den_natCast, mul_one] using Rat.mul_den_dvd a (n : ℚ)

/-- 冪の分母は元の分母の同じ冪を割り切る。 -/
theorem den_pow_dvd_pow_den (a : ℚ) (n : ℕ) :
    (a ^ n).den ∣ a.den ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (Rat.mul_den_dvd _ _).trans (Nat.mul_dvd_mul ih (dvd_refl _))

end ArithLemmas.Mathlib.Rat
