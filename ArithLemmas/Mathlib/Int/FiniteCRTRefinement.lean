module

public import ArithLemmas.Mathlib.Int.FiniteCRTCompatibility

/-!
# 有限合同系への一条件追加：可解性・周期・計数の普遍原理

既に有限個の合同条件を満たす `c` が与えられているとする。
その既存系の周期を `L = s.lcm m` とすれば、新しい条件
`x ≡ u [ZMOD n]` を課した系が可解である必要十分条件は
`c ≡ u [ZMOD gcd L n]` である。

新系が可解なら周期は `lcm L n`、全解集合は一つの合同類であり、
任意の半開整数区間における点数は `residueIndexLength` で正確に与えられる。
この結果は正の法だけでなく、存在・合同類の定理については法 `0` も扱う。

下位層の `Nat/CRT` および `ZMod/CRTCounting` は代表元構成と同値写像を
担当しており、この上位の一般定理をimportしない（循環依存回避）。
-/

public section

namespace ArithLemmas.Mathlib.Int

variable {ι : Type*}

/-- 既存の有限合同系に一条件を追加できるための、GCDによる必要十分条件。 -/
theorem finiteCRT_refine_exists_iff_gcd
    (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ) (c : ℤ)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)]) (n : ℕ) (u : ℤ) :
    (∃ d : ℤ,
      (∀ i ∈ s, d ≡ r i [ZMOD (m i : ℤ)]) ∧
      d ≡ u [ZMOD (n : ℤ)]) ↔
      c ≡ u [ZMOD (Nat.gcd (s.lcm m) n : ℤ)] := by
  have hfamily (x : ℤ) :
      (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ↔
        x ≡ c [ZMOD (↑(s.lcm m : ℕ) : ℤ)] := by
    simpa only [finiteCRT_lcm_natCast s m] using
      finiteCRT_constraints_iff_lcm s (fun i => (m i : ℤ)) r c hc x
  constructor
  · rintro ⟨d, hdS, hdN⟩
    exact crt_compatibility_of_solution (s.lcm m) n c u d
      ((hfamily d).mp hdS) hdN
  · intro h
    obtain ⟨d, hdL, hdN⟩ :=
      (crt_exists_iff_gcd (s.lcm m) n c u).mpr h
    exact ⟨d, (hfamily d).mpr hdL, hdN⟩

/-- 一条件追加が可能であることと、拡張後の解集合が一つのLCM合同類になることは同値。 -/
theorem finiteCRT_refine_coset_iff_gcd
    (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ) (c : ℤ)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)]) (n : ℕ) (u : ℤ) :
    (∃ d : ℤ, ∀ x : ℤ,
      ((∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ∧
          x ≡ u [ZMOD (n : ℤ)]) ↔
        x ≡ d [ZMOD (Nat.lcm (s.lcm m) n : ℤ)]) ↔
      c ≡ u [ZMOD (Nat.gcd (s.lcm m) n : ℤ)] := by
  have hfamily (x : ℤ) :
      (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ↔
        x ≡ c [ZMOD (↑(s.lcm m : ℕ) : ℤ)] := by
    simpa only [finiteCRT_lcm_natCast s m] using
      finiteCRT_constraints_iff_lcm s (fun i => (m i : ℤ)) r c hc x
  constructor
  · rintro ⟨d, hd⟩
    have hsol :
        (∀ i ∈ s, d ≡ r i [ZMOD (m i : ℤ)]) ∧
          d ≡ u [ZMOD (n : ℤ)] :=
      (hd d).mpr (Int.ModEq.refl d)
    exact (finiteCRT_refine_exists_iff_gcd s m r c hc n u).mp
      ⟨d, hsol.1, hsol.2⟩
  · intro h
    obtain ⟨d, hdS, hdN⟩ :=
      (finiteCRT_refine_exists_iff_gcd s m r c hc n u).mpr h
    refine ⟨d, fun x => ?_⟩
    rw [hfamily x]
    exact residue_constraints_iff_lcm ((hfamily d).mp hdS) hdN x

/-- 拡張後の系の二解は、新しいLCM周期で合同である。 -/
theorem finiteCRT_refine_unique_mod_lcm
    (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ)
    (n : ℕ) (u x y : ℤ)
    (hx : (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ∧
      x ≡ u [ZMOD (n : ℤ)])
    (hy : (∀ i ∈ s, y ≡ r i [ZMOD (m i : ℤ)]) ∧
      y ≡ u [ZMOD (n : ℤ)]) :
    x ≡ y [ZMOD (Nat.lcm (s.lcm m) n : ℤ)] := by
  have hL : y ≡ x [ZMOD (↑(s.lcm m : ℕ) : ℤ)] := by
    have h := finiteCRT_constraints_iff_lcm s
      (fun i => (m i : ℤ)) r x hx.1 y
    rw [finiteCRT_lcm_natCast s m] at h
    exact h.mp hy.1
  have hn : y ≡ x [ZMOD (n : ℤ)] :=
    hy.2.trans hx.2.symm
  exact ((residue_constraints_iff_lcm
    (m := s.lcm m) (n := n)
    (Int.ModEq.refl x) (Int.ModEq.refl x) y).mp ⟨hL, hn⟩).symm

/-- 追加した有限合同系の区間計数は、結合LCMを法とする添字長に正確に等しい。 -/
theorem finiteCRT_refine_count_exact
    (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ) (c : ℤ)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)])
    (n : ℕ) (u a b : ℤ)
    (hm : ∀ i ∈ s, 0 < m i) (hn : 0 < n)
    (hcompat : c ≡ u [ZMOD (Nat.gcd (s.lcm m) n : ℤ)]) :
    ∃ d : ℤ,
      (∀ i ∈ s, d ≡ r i [ZMOD (m i : ℤ)]) ∧
      d ≡ u [ZMOD (n : ℤ)] ∧
      (Finset.filter
        (fun x : ℤ => (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ∧
          x ≡ u [ZMOD (n : ℤ)])
        (Finset.Ico a b)).card =
          residueIndexLength a b (Nat.lcm (s.lcm m) n) d := by
  obtain ⟨d, hdS, hdN⟩ :=
    (finiteCRT_refine_exists_iff_gcd s m r c hc n u).mpr hcompat
  have hfamily (x : ℤ) :
      (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ↔
        x ≡ c [ZMOD (↑(s.lcm m : ℕ) : ℤ)] := by
    simpa only [finiteCRT_lcm_natCast s m] using
      finiteCRT_constraints_iff_lcm s (fun i => (m i : ℤ)) r c hc x
  have hperiod : (0 : ℤ) < (Nat.lcm (s.lcm m) n : ℤ) := by
    have hS : s.lcm m ≠ 0 :=
      (Finset.lcm_ne_zero_iff).2 (fun i hi => (hm i hi).ne')
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hS hn.ne')
  have hset :
      Finset.filter
          (fun x : ℤ => (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ∧
            x ≡ u [ZMOD (n : ℤ)]) (Finset.Ico a b) =
        Finset.filter
          (fun x : ℤ => x ≡ d [ZMOD (Nat.lcm (s.lcm m) n : ℤ)])
          (Finset.Ico a b) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hS, hn'⟩
      exact ⟨hx, (residue_constraints_iff_lcm
        ((hfamily d).mp hdS) hdN x).mp ⟨(hfamily x).mp hS, hn'⟩⟩
    · rintro ⟨hx, hmod⟩
      obtain ⟨hL, hn'⟩ := (residue_constraints_iff_lcm
        ((hfamily d).mp hdS) hdN x).mpr hmod
      exact ⟨hx, (hfamily x).mpr hL, hn'⟩
  refine ⟨d, hdS, hdN, ?_⟩
  rw [hset]
  exact (residueIndexLength_eq_card a b
    (Nat.lcm (s.lcm m) n) d hperiod).symm

/-- 一条件を追加した系の区間計数は、幅を周期で割った値から高々1だけずれる。 -/
theorem finiteCRT_refine_count_error
    (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ) (c : ℤ)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)])
    (n : ℕ) (u a b : ℤ) (hab : a ≤ b)
    (hm : ∀ i ∈ s, 0 < m i) (hn : 0 < n)
    (hcompat : c ≡ u [ZMOD (Nat.gcd (s.lcm m) n : ℤ)]) :
    ∃ d : ℤ,
      (∀ i ∈ s, d ≡ r i [ZMOD (m i : ℤ)]) ∧
      d ≡ u [ZMOD (n : ℤ)] ∧
      |((Finset.filter
        (fun x : ℤ => (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ∧
          x ≡ u [ZMOD (n : ℤ)])
        (Finset.Ico a b)).card : ℝ) -
          ((b - a : ℤ) : ℝ) / ((Nat.lcm (s.lcm m) n : ℤ) : ℝ)| ≤ 1 := by
  obtain ⟨d, hdS, hdN, hcount⟩ :=
    finiteCRT_refine_count_exact s m r c hc n u a b hm hn hcompat
  have hperiod : (0 : ℤ) < (Nat.lcm (s.lcm m) n : ℤ) := by
    have hS : s.lcm m ≠ 0 :=
      (Finset.lcm_ne_zero_iff).2 (fun i hi => (hm i hi).ne')
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hS hn.ne')
  refine ⟨d, hdS, hdN, ?_⟩
  rw [hcount]
  exact residueIndexLength_absolute_error a b
    (Nat.lcm (s.lcm m) n) d hab hperiod

/-- GCD整合性が失敗した場合、追加後の系はどの整数区間でも空集合である。 -/
theorem finiteCRT_refine_count_zero_of_incompatible
    (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ) (c : ℤ)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)])
    (n : ℕ) (u a b : ℤ)
    (hbad : ¬ c ≡ u [ZMOD (Nat.gcd (s.lcm m) n : ℤ)]) :
    (Finset.filter
      (fun x : ℤ => (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ∧
        x ≡ u [ZMOD (n : ℤ)])
      (Finset.Ico a b)).card = 0 := by
  classical
  have hno : ¬ ∃ d : ℤ,
      (∀ i ∈ s, d ≡ r i [ZMOD (m i : ℤ)]) ∧
      d ≡ u [ZMOD (n : ℤ)] := by
    intro hd
    exact hbad ((finiteCRT_refine_exists_iff_gcd s m r c hc n u).mp hd)
  have hempty :
      Finset.filter
          (fun x : ℤ => (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ∧
            x ≡ u [ZMOD (n : ℤ)])
          (Finset.Ico a b) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hx
    exact (hno ⟨x, hx.2⟩).elim
  simp [hempty]

/-- 既存LCMと追加法が互いに素なら、追加剰余に制約はない。 -/
theorem finiteCRT_refine_exists_of_coprime
    (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ) (c : ℤ)
    (hc : ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)])
    (n : ℕ) (u : ℤ) (hcop : Nat.Coprime (s.lcm m) n) :
    ∃ d : ℤ,
      (∀ i ∈ s, d ≡ r i [ZMOD (m i : ℤ)]) ∧
      d ≡ u [ZMOD (n : ℤ)] := by
  apply (finiteCRT_refine_exists_iff_gcd s m r c hc n u).mpr
  simpa only [hcop.gcd_eq_one, Nat.cast_one] using
    (Int.modEq_one (a := c) (b := u))

end ArithLemmas.Mathlib.Int
