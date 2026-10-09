module

public import ArithLemmas.Mathlib.Int.CRTInterval
public import ArithLemmas.Mathlib.Int.AffineResidue

/-!
# 一般化中国剰余定理と合同類の正確な計数

二つの自然数の法は互いに素である必要がない。
解の存在は gcd による剰余の整合性と同値であり、解が存在する場合の
全解集合は lcm を周期とする単一の合同類となる。
有限整数区間での正確な解の個数は、既存のアフィン添字長から導出する。

核心となるのは解集合の特徴付けであって、CRT 構成の再実装ではない。
-/

public section

namespace ArithLemmas.Mathlib.Int

/-- 二つの合同条件を同時に満たす数があれば、剰余は gcd を法として整合する。 -/
theorem crt_compatibility_of_solution (m n : ℕ) (u v c : ℤ)
    (hm : c ≡ u [ZMOD (m : ℤ)]) (hn : c ≡ v [ZMOD (n : ℤ)]) :
    u ≡ v [ZMOD (Nat.gcd m n : ℤ)] := by
  have hgm : (Nat.gcd m n : ℤ) ∣ (m : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_left m n
  have hgn : (Nat.gcd m n : ℤ) ∣ (n : ℤ) := by
    exact_mod_cast Nat.gcd_dvd_right m n
  have hu : (Nat.gcd m n : ℤ) ∣ u - c :=
    hgm.trans (Int.modEq_iff_dvd.mp hm)
  have hv : (Nat.gcd m n : ℤ) ∣ v - c :=
    hgn.trans (Int.modEq_iff_dvd.mp hn)
  apply Int.modEq_iff_dvd.mpr
  have hdiff : (Nat.gcd m n : ℤ) ∣ (v - c) - (u - c) := dvd_sub hv hu
  convert hdiff using 1
  ring

/-- 一般化CRTの可解性：二法の合同条件に共通解があることと、gcdでの整合性は同値。 -/
theorem crt_exists_iff_gcd (m n : ℕ) (u v : ℤ) :
    (∃ c : ℤ, c ≡ u [ZMOD (m : ℤ)] ∧ c ≡ v [ZMOD (n : ℤ)]) ↔
      u ≡ v [ZMOD (Nat.gcd m n : ℤ)] := by
  constructor
  · rintro ⟨c, hm, hn⟩
    exact crt_compatibility_of_solution m n u v c hm hn
  · intro h
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h
    have hbez :
        (m : ℤ) * Nat.gcdA m n + (n : ℤ) * Nat.gcdB m n =
          (Nat.gcd m n : ℤ) := by
      simpa only [] using (Nat.gcd_eq_gcd_ab m n).symm
    let c : ℤ := u + (m : ℤ) * Nat.gcdA m n * t
    refine ⟨c, Int.modEq_iff_dvd.mpr ?_, Int.modEq_iff_dvd.mpr ?_⟩
    · refine ⟨-(Nat.gcdA m n * t), ?_⟩
      dsimp [c]
      ring
    · refine ⟨Nat.gcdB m n * t, ?_⟩
      dsimp [c]
      calc
        v - (u + (m : ℤ) * Nat.gcdA m n * t) =
            (v - u) - ((m : ℤ) * Nat.gcdA m n) * t := by ring
        _ = (Nat.gcd m n : ℤ) * t - ((m : ℤ) * Nat.gcdA m n) * t := by
          rw [ht]
        _ = (n : ℤ) * (Nat.gcdB m n * t) := by
          rw [← hbez]
          ring

/-- 既知の同時解を基準にすると、解集合はLCMを法とする一つの合同類。 -/
theorem residue_constraints_iff_lcm {m n : ℕ} {u v c : ℤ}
    (hm : c ≡ u [ZMOD (m : ℤ)]) (hn : c ≡ v [ZMOD (n : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (m : ℤ)] ∧ x ≡ v [ZMOD (n : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm m n : ℤ)] := by
  have hlcm : (m : ℤ).lcm (n : ℤ) = Nat.lcm m n := by
    simp [Int.lcm_def]
  rw [← hlcm, ← Int.modEq_and_modEq_iff_modEq_lcm]
  exact ⟨fun h => ⟨h.1.trans hm.symm, h.2.trans hn.symm⟩,
    fun h => ⟨h.1.trans hm, h.2.trans hn⟩⟩

/-- 解集合が一つのLCM合同類になることと、剰余のgcd整合性は同値。 -/
theorem crt_solution_coset_iff (m n : ℕ) (u v : ℤ) :
    (∃ c : ℤ, ∀ x : ℤ,
      (x ≡ u [ZMOD (m : ℤ)] ∧ x ≡ v [ZMOD (n : ℤ)]) ↔
        x ≡ c [ZMOD (Nat.lcm m n : ℤ)]) ↔
      u ≡ v [ZMOD (Nat.gcd m n : ℤ)] := by
  constructor
  · rintro ⟨c, hc⟩
    have hcc : c ≡ u [ZMOD (m : ℤ)] ∧ c ≡ v [ZMOD (n : ℤ)] :=
      (hc c).mpr (Int.ModEq.refl c)
    exact crt_compatibility_of_solution m n u v c hcc.1 hcc.2
  · intro h
    obtain ⟨c, hm, hn⟩ := (crt_exists_iff_gcd m n u v).mpr h
    exact ⟨c, fun x => residue_constraints_iff_lcm hm hn x⟩

/-- 同じ二合同条件の任意の二解はLCMを法として合同。 -/
theorem crt_solutions_unique_mod_lcm (m n : ℕ) (u v x y : ℤ)
    (hx : x ≡ u [ZMOD (m : ℤ)] ∧ x ≡ v [ZMOD (n : ℤ)])
    (hy : y ≡ u [ZMOD (m : ℤ)] ∧ y ≡ v [ZMOD (n : ℤ)]) :
    x ≡ y [ZMOD (Nat.lcm m n : ℤ)] :=
  ((residue_constraints_iff_lcm hx.1 hx.2 y).mp hy).symm

/-- 解が存在するとき、任意の整数半開区間での正確な解の個数はアフィン添字長。 -/
theorem compatible_residue_count_exact (a b : ℤ) {m n : ℕ}
    (hmpos : 0 < m) (hnpos : 0 < n) {u v c : ℤ}
    (hm : c ≡ u [ZMOD (m : ℤ)]) (hn : c ≡ v [ZMOD (n : ℤ)]) :
    (Finset.filter
      (fun x : ℤ => x ≡ u [ZMOD (m : ℤ)] ∧ x ≡ v [ZMOD (n : ℤ)])
      (Finset.Ico a b)).card = residueIndexLength a b (Nat.lcm m n) c := by
  have hL : (0 : ℤ) < (Nat.lcm m n : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hmpos.ne' hnpos.ne')
  have heq :
      Finset.filter
          (fun x : ℤ => x ≡ u [ZMOD (m : ℤ)] ∧ x ≡ v [ZMOD (n : ℤ)])
          (Finset.Ico a b) =
        Finset.filter (fun x : ℤ => x ≡ c [ZMOD (Nat.lcm m n : ℤ)])
          (Finset.Ico a b) := by
    ext x
    simp only [Finset.mem_filter]
    exact and_congr_right (fun _ => residue_constraints_iff_lcm hm hn x)
  rw [heq]
  exact (residueIndexLength_eq_card a b (Nat.lcm m n) c hL).symm

/-- gcd整合条件が成立しない場合、任意の整数区間における同時解の個数は0。 -/
theorem incompatible_residue_count_zero (a b : ℤ) (m n : ℕ) (u v : ℤ)
    (h : ¬ u ≡ v [ZMOD (Nat.gcd m n : ℤ)]) :
    (Finset.filter
      (fun x : ℤ => x ≡ u [ZMOD (m : ℤ)] ∧ x ≡ v [ZMOD (n : ℤ)])
      (Finset.Ico a b)).card = 0 := by
  classical
  have hempty :
      Finset.filter
          (fun x : ℤ => x ≡ u [ZMOD (m : ℤ)] ∧ x ≡ v [ZMOD (n : ℤ)])
          (Finset.Ico a b) = ∅ := by
    ext x
    constructor
    · intro hx
      have hconstraints := (Finset.mem_filter.mp hx).2
      exact (h (crt_compatibility_of_solution m n u v x
        hconstraints.1 hconstraints.2)).elim
    · intro hx
      simp at hx
  simp only [hempty, Finset.card_empty]

end ArithLemmas.Mathlib.Int
