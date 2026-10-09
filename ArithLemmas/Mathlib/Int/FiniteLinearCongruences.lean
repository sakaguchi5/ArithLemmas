module

public import ArithLemmas.Mathlib.Int.LinearCongruence
public import ArithLemmas.Mathlib.Int.FiniteCRTCompatibility

/-!
# 有限個の一次合同式を有限族CRTへ標準化する

各 `a i * x ≡ b i [ZMOD m i]` を、既知の一解と
縮約周期 `m i / gcd(m i, a i)` の単一合同類に変換する。
全条件の可解性は縮約周期のGCDを法とする対ごとの整合性に一致する。
-/

public section
namespace ArithLemmas.Mathlib.Int

variable {ι : Type*}

/-- 有限個の一次合同式の解集合の共通周期。 -/
def finiteLinearCongruencesPeriod (s : Finset ι) (a : ι → ℤ) (m : ι → ℕ) : ℕ :=
  s.lcm (fun i => linearCongruencePeriod (a i) (m i))

/-- 個々の一次合同式が可解なとき、各解の代表元を選ぶ。 -/
noncomputable def linearCongruenceRepresentative
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (i : ι) : ℤ := by
  classical
  exact if hi : i ∈ s then
    Classical.choose ((linearCongruence_exists_iff_gcd_dvd (a i) (b i) (m i)).mpr
      (hlocal i hi))
  else 0

/-- 選んだ代表元は対応する一次合同式の解である。 -/
theorem linearCongruenceRepresentative_spec
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (i : ι) (hi : i ∈ s) :
    a i * (linearCongruenceRepresentative s a b m hlocal i) ≡ b i
      [ZMOD (m i : ℤ)] := by
  classical
  simp only [linearCongruenceRepresentative, dite_eq_left hi]
  exact Classical.choose_spec
    ((linearCongruence_exists_iff_gcd_dvd (a i) (b i) (m i)).mpr
      (hlocal i hi))

/-- 一次合同式系は、選んだ代表元についての通常の有限CRT系と同値。 -/
theorem finiteLinearCongruences_reduce
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (x : ℤ) :
    (∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)]) ↔
      ∀ i ∈ s,
        x ≡ linearCongruenceRepresentative s a b m hlocal i
          [ZMOD (linearCongruencePeriod (a i) (m i) : ℤ)] := by
  constructor
  · intro hx i hi
    exact (linearCongruence_iff_modEq (a i) (b i) (m i)
      (hm i hi) (linearCongruenceRepresentative s a b m hlocal i)
      (linearCongruenceRepresentative_spec s a b m hlocal i hi) x).mp (hx i hi)
  · intro hx i hi
    exact (linearCongruence_iff_modEq (a i) (b i) (m i)
      (hm i hi) (linearCongruenceRepresentative s a b m hlocal i)
      (linearCongruenceRepresentative_spec s a b m hlocal i hi) x).mpr (hx i hi)

/-- 全法が正のとき、縮約後の共通周期も正。 -/
theorem finiteLinearCongruencesPeriod_pos
    (s : Finset ι) (a : ι → ℤ) (m : ι → ℕ)
    (hm : ∀ i ∈ s, 0 < m i) :
    0 < finiteLinearCongruencesPeriod s a m := by
  unfold finiteLinearCongruencesPeriod
  have hn : s.lcm (fun i => linearCongruencePeriod (a i) (m i)) ≠ 0 :=
    (Finset.lcm_ne_zero_iff).mpr
      (fun i hi => (linearCongruencePeriod_pos (a i) (m i) (hm i hi)).ne')
  exact Nat.pos_of_ne_zero hn

/-- 個々の式が可解なら、同時可解性は縮約周期の対ごとのGCD整合性と同値。 -/
theorem finiteLinearCongruences_exists_iff_pairwise_gcd
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i) :
    (∃ x : ℤ, ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)]) ↔
      ∀ i ∈ s, ∀ j ∈ s,
        linearCongruenceRepresentative s a b m hlocal i ≡
          linearCongruenceRepresentative s a b m hlocal j
          [ZMOD (Nat.gcd
            (linearCongruencePeriod (a i) (m i))
            (linearCongruencePeriod (a j) (m j)) : ℤ)] := by
  have hperiod : ∀ i ∈ s, 0 < linearCongruencePeriod (a i) (m i) :=
    fun i hi => linearCongruencePeriod_pos (a i) (m i) (hm i hi)
  exact (exists_congr (fun x =>
    finiteLinearCongruences_reduce s a b m hm hlocal x)).trans
    (finiteCRT_exists_iff_pairwise_gcd s
      (fun i => linearCongruencePeriod (a i) (m i))
      (linearCongruenceRepresentative s a b m hlocal) hperiod)

/-- 完全な可解性判定：局所GCD整除性と縮約された有限族CRTの整合性。 -/
theorem finiteLinearCongruences_exists_iff
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ)
    (hm : ∀ i ∈ s, 0 < m i) :
    (∃ x : ℤ, ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)]) ↔
      ∃ hlocal : (∀ i ∈ s,
          ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i),
        ∀ i ∈ s, ∀ j ∈ s,
          linearCongruenceRepresentative s a b m hlocal i ≡
            linearCongruenceRepresentative s a b m hlocal j
            [ZMOD (Nat.gcd
              (linearCongruencePeriod (a i) (m i))
              (linearCongruencePeriod (a j) (m j)) : ℤ)] := by
  constructor
  · rintro ⟨x, hx⟩
    have hlocal : ∀ i ∈ s,
        ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i := by
      intro i hi
      exact (linearCongruence_exists_iff_gcd_dvd (a i) (b i) (m i)).mp
        ⟨x, hx i hi⟩
    exact ⟨hlocal,
      (finiteLinearCongruences_exists_iff_pairwise_gcd s a b m hm hlocal).mp
        ⟨x, hx⟩⟩
  · rintro ⟨hlocal, hp⟩
    exact (finiteLinearCongruences_exists_iff_pairwise_gcd s a b m hm hlocal).mpr hp

/-- 共通解を代表とすると、全解集合は縮約法の有限LCMに対する一つの合同類。 -/
theorem finiteLinearCongruences_iff_lcm
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (c : ℤ) (hc : ∀ i ∈ s, a i * c ≡ b i [ZMOD (m i : ℤ)])
    (x : ℤ) :
    (∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)]) ↔
      x ≡ c [ZMOD (finiteLinearCongruencesPeriod s a m : ℤ)] := by
  have hcc : ∀ i ∈ s,
      c ≡ linearCongruenceRepresentative s a b m hlocal i
        [ZMOD (linearCongruencePeriod (a i) (m i) : ℤ)] :=
    (finiteLinearCongruences_reduce s a b m hm hlocal c).mp hc
  have h := (finiteLinearCongruences_reduce s a b m hm hlocal x).trans
    (finiteCRT_constraints_iff_lcm s
      (fun i => (linearCongruencePeriod (a i) (m i) : ℤ))
      (linearCongruenceRepresentative s a b m hlocal) c hcc x)
  simpa only [finiteLinearCongruencesPeriod, finiteCRT_lcm_natCast] using h

/-- 同じ系の二つの解は縮約周期の有限LCMを法として合同。 -/
theorem finiteLinearCongruences_unique_mod_lcm
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (x y : ℤ)
    (hx : ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)])
    (hy : ∀ i ∈ s, a i * y ≡ b i [ZMOD (m i : ℤ)]) :
    x ≡ y [ZMOD (finiteLinearCongruencesPeriod s a m : ℤ)] :=
  (finiteLinearCongruences_iff_lcm s a b m hm hlocal y hy x).mp hx

end ArithLemmas.Mathlib.Int
