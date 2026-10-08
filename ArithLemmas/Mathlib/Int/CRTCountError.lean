module

public import ArithLemmas.Mathlib.Int.CRTInterval
public import ArithLemmas.Mathlib.Int.ResidueInterval
/-!
# 複数合同条件の統合と整数区間の計数誤差（第4段階4E-2）

原典：`OAI/Combinatorics/Progressions/Lattices/ResidueSliceCountingCost.lean`。
合同条件を最小公倍数を法とする一つの条件へ統合し、
既存の第4段階4Bの誤差評価を二剰余条件へ拡張する。
-/

public section

namespace ArithLemmas.Mathlib.Int

/-- 二つの剰余条件を、既知の同時解を代表とするLCM合同へ統合する。 -/
theorem residue_constraints_iff_lcm {M d : ℕ} {u v c : ℤ}
    (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d : ℤ)] := by
  have hlcm : (M : ℤ).lcm (d : ℤ) = Nat.lcm M d := by simp [Int.lcm_def]
  rw [← hlcm, ← Int.modEq_and_modEq_iff_modEq_lcm]
  exact ⟨fun h => ⟨h.1.trans hM.symm, h.2.trans hd.symm⟩,
    fun h => ⟨h.1.trans hM, h.2.trans hd⟩⟩

/-- 互いに素な二法の任意の整数剰余を同時に満たす整数が存在する。 -/
theorem exists_integer_coprime_residues {M d : ℕ} (hcop : M.Coprime d) (u v : ℤ) :
    ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] := by
  have hbez : (M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d = 1 := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab M d).symm
  let c := u * ((d : ℤ) * Nat.gcdB M d) + v * ((M : ℤ) * Nat.gcdA M d)
  refine ⟨c, Int.modEq_iff_dvd.mpr ?_, Int.modEq_iff_dvd.mpr ?_⟩
  · refine ⟨(u - v) * Nat.gcdA M d, ?_⟩
    calc
      u - c = u * ((M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d) - c := by
        rw [hbez, mul_one]
      _ = (M : ℤ) * ((u - v) * Nat.gcdA M d) := by dsimp [c]; ring
  · refine ⟨(v - u) * Nat.gcdB M d, ?_⟩
    calc
      v - c = v * ((M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d) - c := by
        rw [hbez, mul_one]
      _ = (d : ℤ) * ((v - u) * Nat.gcdB M d) := by dsimp [c]; ring

/-- 追加の法と既存二法の積が互いに素なら、第三の合同条件を課しても解がある。 -/
theorem coprime_refinement_preserves_compatibility {M d J : ℕ}
    (hcop : (M * d).Coprime J) (u v w : ℤ) :
    (∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)]) ↔
      ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] ∧
        c ≡ w [ZMOD (J : ℤ)] := by
  constructor
  · rintro ⟨c, hM, hd⟩
    have hL : (Nat.lcm M d).Coprime J := hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
    obtain ⟨t, ht, htJ⟩ := exists_integer_coprime_residues hL c w
    obtain ⟨htM, htd⟩ := (residue_constraints_iff_lcm hM hd t).mpr ht
    exact ⟨t, htM, htd, htJ⟩
  · rintro ⟨c, hM, hd, _⟩
    exact ⟨c, hM, hd⟩

/-- 三つの合同条件を、LCMと互いに素な第三法の積へ統合する。 -/
theorem refined_residue_constraints_iff {M d J : ℕ} (hcop : (M * d).Coprime J)
    {u v w c : ℤ} (hM : c ≡ u [ZMOD (M : ℤ)])
    (hd : c ≡ v [ZMOD (d : ℤ)]) (hJ : c ≡ w [ZMOD (J : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)] ∧
      x ≡ w [ZMOD (J : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d * J : ℤ)] := by
  have hL : (Nat.lcm M d).Coprime J := hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
  rw [← and_assoc, residue_constraints_iff_lcm hM hd x,
    residue_constraints_iff_lcm (Int.ModEq.refl c) hJ x, hL.lcm_eq_mul]
  simp only [Nat.cast_mul]

/-- 整数区間の二重合同条件の出現個数は、幅/LCMから高々1だけずれる。 -/
theorem compatible_residue_count_error (a b : ℤ) (hab : a ≤ b) {M d : ℕ}
    (hMpos : 0 < M) (hdpos : 0 < d) {u v c : ℤ}
    (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)]) :
    |((Finset.filter (fun x => x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)])
      (Finset.Ico a b)).card : ℝ) - ((b - a : ℤ) : ℝ) / Nat.lcm M d| ≤ 1 := by
  have hp : (0 : ℤ) < Nat.lcm M d := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hMpos.ne' hdpos.ne')
  have heq :
      Finset.filter (fun x : ℤ => x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)])
          (Finset.Ico a b) =
        Finset.filter (fun x : ℤ => x ≡ c [ZMOD (Nat.lcm M d : ℤ)])
          (Finset.Ico a b) := by
    ext x
    simp only [Finset.mem_filter, residue_constraints_iff_lcm hM hd x]
  rw [heq]
  exact residue_card_absolute_error a b (Nat.lcm M d) c hab hp

end ArithLemmas.Mathlib.Int
