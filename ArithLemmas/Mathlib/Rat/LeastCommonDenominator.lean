module

public import ArithLemmas.Mathlib.Rat.DenominatorArithmetic

/-!
# 有限個の有理数に対する最小共通分母

各有理数の既約分母の最小公倍数を、有限集合の標準的な共通分母とする。
この数は、単なる有限和の分母の上界ではなく、
「すべての分母を割り切らせる数のうち最小」という普遍的性質で
特徴付けられる。空の有限集合の場合も含み、その値は `1` である。
-/

public section

namespace ArithLemmas.Mathlib.Rat

variable {ι : Type*}

/-- 有限個の有理数に対する、整除関係で最小の標準的な共通分母。 -/
@[expose] def leastCommonDenominator (s : Finset ι) (f : ι → ℚ) : ℕ :=
  s.lcm (fun i => (f i).den)

/-- **普遍的性質。** すべての既約分母が `D` を割り切ることと、
それらの最小公倍数が `D` を割り切ることは同値である。 -/
theorem leastCommonDenominator_dvd_iff (s : Finset ι) (f : ι → ℚ) (D : ℕ) :
    leastCommonDenominator s f ∣ D ↔
      ∀ i ∈ s, (f i).den ∣ D := by
  unfold leastCommonDenominator
  exact Finset.lcm_dvd_iff

/-- 有限集合の各有理数の既約分母は、標準共通分母を割り切る。 -/
theorem den_dvd_leastCommonDenominator (s : Finset ι) (f : ι → ℚ)
    (i : ι) (hi : i ∈ s) :
    (f i).den ∣ leastCommonDenominator s f :=
  (leastCommonDenominator_dvd_iff s f _).mp dvd_rfl i hi

/-- 任意の共通分母は、標準共通分母の倍数となる。 -/
theorem leastCommonDenominator_dvd_of_common (s : Finset ι)
    (f : ι → ℚ) (D : ℕ) (h : ∀ i ∈ s, (f i).den ∣ D) :
    leastCommonDenominator s f ∣ D :=
  (leastCommonDenominator_dvd_iff s f D).mpr h

/-- 標準共通分母は、有限集合が空の場合も含めて正である。 -/
theorem leastCommonDenominator_pos (s : Finset ι) (f : ι → ℚ) :
    0 < leastCommonDenominator s f := by
  apply Nat.pos_of_ne_zero
  change s.lcm (fun i => (f i).den) ≠ 0
  exact (Finset.lcm_ne_zero_iff).mpr (fun i hi => Rat.den_ne_zero (f i))

/-- 整除関係についての最小性から、正の共通分母の間での
自然数の大小関係についての最小性も従う。 -/
theorem leastCommonDenominator_le_of_common (s : Finset ι)
    (f : ι → ℚ) (D : ℕ) (hD : 0 < D)
    (h : ∀ i ∈ s, (f i).den ∣ D) :
    leastCommonDenominator s f ≤ D :=
  Nat.le_of_dvd hD (leastCommonDenominator_dvd_of_common s f D h)

/-- 自然数が標準共通分母に一致することと、すべての分母を割り切らせ、
さらに他のあらゆる共通分母を割り切ることは同値である。 -/
theorem eq_leastCommonDenominator_iff (s : Finset ι)
    (f : ι → ℚ) (D : ℕ) :
    D = leastCommonDenominator s f ↔
      (∀ i ∈ s, (f i).den ∣ D) ∧
      (∀ N : ℕ, (∀ i ∈ s, (f i).den ∣ N) → D ∣ N) := by
  constructor
  · rintro rfl
    exact ⟨(leastCommonDenominator_dvd_iff s f _).mp dvd_rfl,
      fun N h => (leastCommonDenominator_dvd_iff s f N).mpr h⟩
  · rintro ⟨hcommon, hleast⟩
    apply Nat.dvd_antisymm
    · exact hleast _ ((leastCommonDenominator_dvd_iff s f _).mp dvd_rfl)
    · exact (leastCommonDenominator_dvd_iff s f D).mpr hcommon

/-- 有理数の有限和の既約分母は、標準共通分母を割り切る。 -/
theorem den_sum_dvd_leastCommonDenominator (s : Finset ι) (f : ι → ℚ) :
    (∑ i ∈ s, f i).den ∣ leastCommonDenominator s f :=
  den_sum_dvd_of_forall s f _ (fun i hi => den_dvd_leastCommonDenominator s f i hi)

/-- 自然数の通常の大小関係において最小の正の共通分母は、
標準共通分母と一意に一致する。 -/
theorem leastCommonDenominator_eq_of_minimal (s : Finset ι)
    (f : ι → ℚ) (D : ℕ)
    (hDpos : 0 < D)
    (hD : ∀ i ∈ s, (f i).den ∣ D)
    (hmin : ∀ N : ℕ, 0 < N →
      (∀ i ∈ s, (f i).den ∣ N) → D ≤ N) :
    D = leastCommonDenominator s f := by
  apply Nat.le_antisymm
  · exact hmin _ (leastCommonDenominator_pos s f)
      ((leastCommonDenominator_dvd_iff s f _).mp dvd_rfl)
  · exact leastCommonDenominator_le_of_common s f D hDpos hD

end ArithLemmas.Mathlib.Rat
