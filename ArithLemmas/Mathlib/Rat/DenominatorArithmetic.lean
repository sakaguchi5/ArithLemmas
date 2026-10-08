module

public import ArithLemmas.Mathlib.Rat.ArithmeticBridge
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# 有理数の分母の整除性（第4段階4E-5）

有理数の和・差・積および有限和・有限積の分母を、一つの自然数で統制する。
原典：`OAI/Computability/MinUncut/Search/RationalDenominatorArithmetic.lean`
および `OAI/Combinatorics/SumProduct/Alignment/TriangularDenominators01.lean`。
既存 Mathlib の `Rat.*_den_dvd_*` を再利用する。
-/

public section

namespace ArithLemmas.Mathlib.Rat

/-- 有理数の有限族に共通する分母として、個々の既約分母の積を使う。 -/
@[expose] def commonDenominator {ι : Type*} (s : Finset ι) (f : ι → ℚ) : ℕ :=
  ∏ i ∈ s, (f i).den

/-- 共通分母は有限集合が空の場合も正である。 -/
theorem commonDenominator_pos {ι : Type*} (s : Finset ι) (f : ι → ℚ) :
    0 < commonDenominator s f := by
  classical
  unfold commonDenominator
  exact Finset.prod_pos (fun i _ => (f i).den_pos)

/-- 族の各要素の既約分母は、共通分母を割り切る。 -/
theorem denominator_dvd_common {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (i : ι) (hi : i ∈ s) :
    (f i).den ∣ commonDenominator s f := by
  classical
  unfold commonDenominator
  exact Finset.dvd_prod_of_mem (fun i => (f i).den) hi

/-- 二つの有理数の分母が同じ自然数を割れば、その和の分母も割る。 -/
theorem den_add_dvd_common {a b : ℚ} {D : ℕ}
    (ha : a.den ∣ D) (hb : b.den ∣ D) :
    (a + b).den ∣ D :=
  (Rat.add_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

/-- 共通分母は有理数の差でも保たれる。 -/
theorem den_sub_dvd_common {a b : ℚ} {D : ℕ}
    (ha : a.den ∣ D) (hb : b.den ∣ D) :
    (a - b).den ∣ D :=
  (Rat.sub_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)

/-- 積の既約分母は二つの上界の積を割り切る。 -/
theorem den_mul_dvd_common {a b : ℚ} {A B : ℕ}
    (ha : a.den ∣ A) (hb : b.den ∣ B) :
    (a * b).den ∣ A * B :=
  (Rat.mul_den_dvd a b).trans (Nat.mul_dvd_mul ha hb)

/-- 有理数に自然数を掛けても既約分母に新しい素因子は生じない。 -/
theorem den_mul_nat_dvd_self (a : ℚ) (n : ℕ) :
    (a * (n : ℚ)).den ∣ a.den := by
  simpa only [Rat.den_natCast, mul_one] using Rat.mul_den_dvd a (n : ℚ)

/-- 自然数回の冪の既約分母は、元の分母の対応する冪を割る。 -/
theorem den_pow_dvd_pow_den (a : ℚ) (n : ℕ) :
    (a ^ n).den ∣ a.den ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (Rat.mul_den_dvd _ _).trans (Nat.mul_dvd_mul ih (dvd_refl _))

/-- 有限和の既約分母は共通分母を割り切る。 -/
theorem den_sum_dvd_commonDenominator {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ commonDenominator s f := by
  classical
  unfold commonDenominator
  exact Finset.Rat.den_sum_dvd_prod_den s f

/-- 有限積の既約分母も共通分母を割り切る。 -/
theorem den_prod_dvd_commonDenominator {ι : Type*}
    (s : Finset ι) (f : ι → ℚ) :
    (∏ i ∈ s, f i).den ∣ commonDenominator s f := by
  classical
  unfold commonDenominator
  exact Finset.Rat.den_prod_dvd_prod_den s f

/-- 族の全分母が一つの数を割り切るなら、有限和もその数を分母にできる。 -/
theorem den_sum_dvd_of_forall {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (D : ℕ)
    (h : ∀ i ∈ s, (f i).den ∣ D) :
    (∑ i ∈ s, f i).den ∣ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      apply den_add_dvd_common
      · exact h i (Finset.mem_insert_self i s)
      · exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj))

end ArithLemmas.Mathlib.Rat
