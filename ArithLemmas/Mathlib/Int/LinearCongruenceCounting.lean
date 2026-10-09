module

public import ArithLemmas.Mathlib.Int.FiniteLinearCongruences

/-!
# 一次合同式系の整数区間内の正確な計数

各一次合同式をGCD標準形へ縮約した後、既存のアフィン整数添字長を使用する。
区間内解数の計算は合同式の個数や係数の形に依存せず、
縮約後の全法のLCMと一つの共通解だけで記述できる。
-/

public section
namespace ArithLemmas.Mathlib.Int

variable {ι : Type*}

/-- 単一の一次合同式の半開整数区間内での解数の正確な公式。 -/
theorem linearCongruence_count_exact
    (a b : ℤ) (m : ℕ) (hm : 0 < m) (A B c : ℤ)
    (hc : a * c ≡ b [ZMOD (m : ℤ)]) :
    (Finset.filter (fun x : ℤ => a * x ≡ b [ZMOD (m : ℤ)])
      (Finset.Ico A B)).card =
      residueIndexLength A B (linearCongruencePeriod a m) c := by
  have hp : (0 : ℤ) < (linearCongruencePeriod a m : ℤ) := by
    exact_mod_cast linearCongruencePeriod_pos a m hm
  have hset :
      Finset.filter (fun x : ℤ => a * x ≡ b [ZMOD (m : ℤ)])
          (Finset.Ico A B) =
        Finset.filter (fun x : ℤ =>
          x ≡ c [ZMOD (linearCongruencePeriod a m : ℤ)])
          (Finset.Ico A B) := by
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => linearCongruence_iff_modEq a b m hm c hc x)
  rw [hset]
  exact (residueIndexLength_eq_card A B (linearCongruencePeriod a m) c hp).symm

/-- 単一の一次合同式の解数と周期による密度の差は高々1。 -/
theorem linearCongruence_count_error
    (a b : ℤ) (m : ℕ) (hm : 0 < m) (A B c : ℤ)
    (hAB : A ≤ B) (hc : a * c ≡ b [ZMOD (m : ℤ)]) :
    |((Finset.filter (fun x : ℤ => a * x ≡ b [ZMOD (m : ℤ)])
      (Finset.Ico A B)).card : ℝ) -
      ((B - A : ℤ) : ℝ) / (linearCongruencePeriod a m : ℝ)| ≤ 1 := by
  rw [linearCongruence_count_exact a b m hm A B c hc]
  have hp : (0 : ℤ) < (linearCongruencePeriod a m : ℤ) := by
    exact_mod_cast linearCongruencePeriod_pos a m hm
  exact residueIndexLength_absolute_error A B (linearCongruencePeriod a m) c hAB hp

/-- 可解な有限個の一次合同式の区間内解数は、LCM周期の添字長に正確に等しい。 -/
theorem finiteLinearCongruences_count_exact
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ) (A B c : ℤ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (hc : ∀ i ∈ s, a i * c ≡ b i [ZMOD (m i : ℤ)]) :
    (Finset.filter (fun x : ℤ =>
        ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)])
        (Finset.Ico A B)).card =
      residueIndexLength A B (finiteLinearCongruencesPeriod s a m) c := by
  have hperiod : (0 : ℤ) < (finiteLinearCongruencesPeriod s a m : ℤ) := by
    exact_mod_cast finiteLinearCongruencesPeriod_pos s a m hm
  have hset :
      Finset.filter (fun x : ℤ =>
          ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)])
          (Finset.Ico A B) =
        Finset.filter (fun x : ℤ =>
          x ≡ c [ZMOD (finiteLinearCongruencesPeriod s a m : ℤ)])
          (Finset.Ico A B) := by
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ =>
      finiteLinearCongruences_iff_lcm s a b m hm hlocal c hc x)
  rw [hset]
  exact (residueIndexLength_eq_card A B
    (finiteLinearCongruencesPeriod s a m) c hperiod).symm

/-- 正確な計数から従う、周期あたり密度に関する誤差評価。 -/
theorem finiteLinearCongruences_count_error
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ) (A B c : ℤ)
    (hAB : A ≤ B) (hm : ∀ i ∈ s, 0 < m i)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (hc : ∀ i ∈ s, a i * c ≡ b i [ZMOD (m i : ℤ)]) :
    |((Finset.filter (fun x : ℤ =>
        ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)])
        (Finset.Ico A B)).card : ℝ) -
      ((B - A : ℤ) : ℝ) / ((finiteLinearCongruencesPeriod s a m : ℕ) : ℝ)| ≤ 1 := by
  rw [finiteLinearCongruences_count_exact s a b m A B c hm hlocal hc]
  have hp : (0 : ℤ) < (finiteLinearCongruencesPeriod s a m : ℤ) := by
    exact_mod_cast finiteLinearCongruencesPeriod_pos s a m hm
  exact residueIndexLength_absolute_error A B
    (finiteLinearCongruencesPeriod s a m) c hAB hp

/-- 局所可解性と対ごとのGCD整合性から、共通解と正確な計数を同時に得る。 -/
theorem finiteLinearCongruences_count_exact_of_pairwise_gcd
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ) (A B : ℤ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (hp : ∀ i ∈ s, ∀ j ∈ s,
      linearCongruenceRepresentative s a b m hlocal i ≡
        linearCongruenceRepresentative s a b m hlocal j
        [ZMOD (Nat.gcd
          (linearCongruencePeriod (a i) (m i))
          (linearCongruencePeriod (a j) (m j)) : ℤ)]) :
    ∃ c : ℤ,
      (∀ i ∈ s, a i * c ≡ b i [ZMOD (m i : ℤ)]) ∧
      (Finset.filter (fun x : ℤ =>
          ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)])
          (Finset.Ico A B)).card =
        residueIndexLength A B (finiteLinearCongruencesPeriod s a m) c := by
  obtain ⟨c, hc⟩ :=
    (finiteLinearCongruences_exists_iff_pairwise_gcd s a b m hm hlocal).mpr hp
  exact ⟨c, hc, finiteLinearCongruences_count_exact s a b m A B c hm hlocal hc⟩

/-- どれか一つでも局所GCD条件が破れれば、系の解は区間に存在しない。 -/
theorem finiteLinearCongruences_count_zero_of_local_obstruction
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ) (A B : ℤ)
    (i : ι) (hi : i ∈ s)
    (hbad : ¬ (((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)) :
    (Finset.filter (fun x : ℤ =>
        ∀ j ∈ s, a j * x ≡ b j [ZMOD (m j : ℤ)])
        (Finset.Ico A B)).card = 0 := by
  classical
  have hno : ¬ ∃ x : ℤ,
      ∀ j ∈ s, a j * x ≡ b j [ZMOD (m j : ℤ)] := by
    rintro ⟨x, hx⟩
    exact hbad ((linearCongruence_exists_iff_gcd_dvd (a i) (b i) (m i)).mp
      ⟨x, hx i hi⟩)
  have hset : Finset.filter (fun x : ℤ =>
        ∀ j ∈ s, a j * x ≡ b j [ZMOD (m j : ℤ)])
        (Finset.Ico A B) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hx
    exact (hno ⟨x, hx.2⟩).elim
  simp [hset]

/-- 局所解がすべてあっても、縮約後の剰余がGCD非整合なら解はゼロ個。 -/
theorem finiteLinearCongruences_count_zero_of_incompatible
    (s : Finset ι) (a b : ι → ℤ) (m : ι → ℕ) (A B : ℤ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hlocal : ∀ i ∈ s, ((Int.gcd (m i : ℤ) (a i) : ℕ) : ℤ) ∣ b i)
    (hbad : ¬ ∀ i ∈ s, ∀ j ∈ s,
      linearCongruenceRepresentative s a b m hlocal i ≡
        linearCongruenceRepresentative s a b m hlocal j
        [ZMOD (Nat.gcd
          (linearCongruencePeriod (a i) (m i))
          (linearCongruencePeriod (a j) (m j)) : ℤ)]) :
    (Finset.filter (fun x : ℤ =>
        ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)])
        (Finset.Ico A B)).card = 0 := by
  classical
  have hno : ¬ ∃ x : ℤ,
      ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)] := by
    intro hx
    exact hbad
      ((finiteLinearCongruences_exists_iff_pairwise_gcd s a b m hm hlocal).mp hx)
  have hset : Finset.filter (fun x : ℤ =>
        ∀ i ∈ s, a i * x ≡ b i [ZMOD (m i : ℤ)])
        (Finset.Ico A B) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hx
    exact (hno ⟨x, hx.2⟩).elim
  simp [hset]

end ArithLemmas.Mathlib.Int
