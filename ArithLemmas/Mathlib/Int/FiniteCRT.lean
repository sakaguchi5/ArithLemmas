module

public import ArithLemmas.Mathlib.Int.GeneralizedCRT
public import Mathlib.Data.Nat.ChineseRemainder
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat

/-!
# 有限個の合同条件：LCM による周期・正確な計数

任意の有限個の整数法（互いに素とは限らない）に対して、
「全ての合同条件を同時に満たす」という関係を、有限 LCM を
法とする単一の合同関係に帰着させる。

解が存在すればその全体は一つの合同類であり、任意の整数区間内での
正確な解の個数は、既存のアフィン添字長で与えられる。

また、二法の一般化 CRT から対ごとの GCD 整合性の必要性を導き、
相異なる法が互いに素な場合の存在定理は Mathlib の
`Nat.chineseRemainderOfFinset` から直接導出する。
-/

public section

open scoped Function

namespace ArithLemmas.Mathlib.Int

variable {ι : Type*}

/-- 有限個の法での同時合同は、その有限 LCM を法とする合同と同値。 -/
theorem finiteCRT_modEq_iff_lcm (s : Finset ι) (m : ι → ℤ) (x y : ℤ) :
    (∀ i ∈ s, x ≡ y [ZMOD m i]) ↔
      x ≡ y [ZMOD s.lcm m] := by
  simpa only [Int.modEq_iff_dvd] using
    ((Finset.lcm_dvd_iff (s := s) (f := m) (a := y - x))).symm

/-- 全ての法が正なら、有限 LCM も正（空集合の場合は `1`）。 -/
theorem finiteCRT_lcm_pos (s : Finset ι) (m : ι → ℤ)
    (hm : ∀ i ∈ s, 0 < m i) :
    0 < s.lcm m := by
  classical
  have hn : s.lcm m ≠ 0 :=
    (Finset.lcm_ne_zero_iff).2 (fun i hi => ne_of_gt (hm i hi))
  have hnonneg : 0 ≤ s.lcm m := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.lcm_insert]
        exact Int.lcm_nonneg _ _
  omega

/-- 既知の同時解を代表として、有限個の合同制約を一つの合同類へ統合する。 -/
theorem finiteCRT_constraints_iff_lcm (s : Finset ι)
    (m r : ι → ℤ) (c : ℤ)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD m i]) (x : ℤ) :
    (∀ i ∈ s, x ≡ r i [ZMOD m i]) ↔
      x ≡ c [ZMOD s.lcm m] := by
  rw [← finiteCRT_modEq_iff_lcm s m x c]
  constructor
  · intro hx i hi
    exact (hx i hi).trans (hc i hi).symm
  · intro hx i hi
    exact (hx i hi).trans (hc i hi)

/-- 解集合が LCM 合同類で表せることと、同時解の存在は同値。 -/
theorem finiteCRT_coset_iff_exists (s : Finset ι) (m r : ι → ℤ) :
    (∃ c : ℤ, ∀ x : ℤ,
      (∀ i ∈ s, x ≡ r i [ZMOD m i]) ↔
        x ≡ c [ZMOD s.lcm m]) ↔
      ∃ c : ℤ, ∀ i ∈ s, c ≡ r i [ZMOD m i] := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, (hc c).mpr (Int.ModEq.refl c)⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun x => finiteCRT_constraints_iff_lcm s m r c hc x⟩

/-- 任意の二つの同時解は、全ての法の LCM を法として合同。 -/
theorem finiteCRT_unique_mod_lcm (s : Finset ι) (m r : ι → ℤ)
    (x y : ℤ)
    (hx : ∀ i ∈ s, x ≡ r i [ZMOD m i])
    (hy : ∀ i ∈ s, y ≡ r i [ZMOD m i]) :
    x ≡ y [ZMOD s.lcm m] :=
  ((finiteCRT_constraints_iff_lcm s m r x hx y).mp hy).symm

/-- 同時解が存在すれば、半開整数区間内の解の個数は正確に求まる。 -/
theorem finiteCRT_count_exact (s : Finset ι) (m r : ι → ℤ)
    (a b c : ℤ) (hm : ∀ i ∈ s, 0 < m i)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD m i]) :
    (Finset.filter (fun x : ℤ => ∀ i ∈ s, x ≡ r i [ZMOD m i])
      (Finset.Ico a b)).card =
      residueIndexLength a b (s.lcm m) c := by
  have hp : 0 < s.lcm m := finiteCRT_lcm_pos s m hm
  have heq :
      Finset.filter (fun x : ℤ => ∀ i ∈ s, x ≡ r i [ZMOD m i])
          (Finset.Ico a b) =
        Finset.filter (fun x : ℤ => x ≡ c [ZMOD s.lcm m])
          (Finset.Ico a b) := by
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => finiteCRT_constraints_iff_lcm s m r c hc x)
  rw [heq]
  exact (residueIndexLength_eq_card a b (s.lcm m) c hp).symm

/-- 正確な個数公式の系：同時解の個数の誤差は `1` 以下。 -/
theorem finiteCRT_count_error (s : Finset ι) (m r : ι → ℤ)
    (a b c : ℤ) (hab : a ≤ b)
    (hm : ∀ i ∈ s, 0 < m i)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD m i]) :
    |((Finset.filter (fun x : ℤ =>
        ∀ i ∈ s, x ≡ r i [ZMOD m i])
        (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / ((s.lcm m : ℤ) : ℝ)| ≤ 1 := by
  rw [finiteCRT_count_exact s m r a b c hm hc]
  exact residueIndexLength_absolute_error a b (s.lcm m) c hab
    (finiteCRT_lcm_pos s m hm)

/-- 二つの法の GCD 整合性は、有限個の合同条件の可解性に必要。 -/
theorem finiteCRT_pairwise_necessary (s : Finset ι)
    (m : ι → ℕ) (r : ι → ℤ)
    (h : ∃ c : ℤ, ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)]) :
    ∀ i ∈ s, ∀ j ∈ s,
      r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)] := by
  obtain ⟨c, hc⟩ := h
  intro i hi j hj
  exact crt_compatibility_of_solution (m i) (m j)
    (r i) (r j) c (hc i hi) (hc j hj)

/-- どれか二条件が GCD に関して非整合なら、区間内の解は `0` 個。 -/
theorem finiteCRT_count_zero_of_incompatible_pair (s : Finset ι)
    (m : ι → ℕ) (r : ι → ℤ) (a b : ℤ)
    (i j : ι) (hi : i ∈ s) (hj : j ∈ s)
    (hbad : ¬ r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)]) :
    (Finset.filter
      (fun x : ℤ => ∀ k ∈ s, x ≡ r k [ZMOD (m k : ℤ)])
      (Finset.Ico a b)).card = 0 := by
  have hn : ∀ x : ℤ, ¬ (∀ k ∈ s, x ≡ r k [ZMOD (m k : ℤ)]) := by
    intro x hx
    exact hbad (crt_compatibility_of_solution (m i) (m j)
      (r i) (r j) x (hx i hi) (hx j hj))
  have he :
      Finset.filter
          (fun x : ℤ => ∀ k ∈ s, x ≡ r k [ZMOD (m k : ℤ)])
          (Finset.Ico a b) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hx
    exact (hn x hx.2).elim
  simp only [he, Finset.card_empty]

/-- 法が有限集合上で互いに素なら、指定した自然数剰余を満たす同時解が存在する。 -/
theorem finiteCRT_exists_of_pairwise_coprime (s : Finset ι)
    (a m : ι → ℕ)
    (hm : ∀ i ∈ s, m i ≠ 0)
    (hcop : Set.Pairwise s (Nat.Coprime on m)) :
    ∃ x : ℕ, ∀ i ∈ s, x ≡ a i [MOD m i] := by
  exact ⟨(Nat.chineseRemainderOfFinset a m s hm hcop).val,
    (Nat.chineseRemainderOfFinset a m s hm hcop).property⟩

end ArithLemmas.Mathlib.Int
