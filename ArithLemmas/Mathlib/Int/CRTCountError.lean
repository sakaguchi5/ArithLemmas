module

public import ArithLemmas.Mathlib.Int.GeneralizedCRT

/-!
# 一般化CRTの系：互いに素な場合の存在性・追加合同条件・計数誤差

解集合をLCMを法とする合同類に同一視する原理は `GeneralizedCRT` に置く。
このファイルには、その直接の系である特殊化と評価のみを残す。
-/

public section

namespace ArithLemmas.Mathlib.Int

/-- 互いに素な二法ではgcd整合性が自動的に成立し、任意の剰余が両立する。 -/
theorem exists_integer_coprime_residues {M d : ℕ} (hcop : M.Coprime d) (u v : ℤ) :
    ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] := by
  apply (crt_exists_iff_gcd M d u v).mpr
  simpa only [hcop.gcd_eq_one, Nat.cast_one] using
    (Int.modEq_one (a := u) (b := v))

/-- 第三法が前二法の積と互いに素なら、両立する合同条件を任意の第三剰余へ拡張できる。 -/
theorem coprime_refinement_preserves_compatibility {M d J : ℕ}
    (hcop : (M * d).Coprime J) (u v w : ℤ) :
    (∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)]) ↔
      ∃ c : ℤ, c ≡ u [ZMOD (M : ℤ)] ∧ c ≡ v [ZMOD (d : ℤ)] ∧
        c ≡ w [ZMOD (J : ℤ)] := by
  constructor
  · rintro ⟨c, hM, hd⟩
    have hL : (Nat.lcm M d).Coprime J :=
      hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
    obtain ⟨t, ht, htJ⟩ := exists_integer_coprime_residues hL c w
    obtain ⟨htM, htd⟩ := (residue_constraints_iff_lcm hM hd t).mpr ht
    exact ⟨t, htM, htd, htJ⟩
  · rintro ⟨c, hM, hd, _⟩
    exact ⟨c, hM, hd⟩

/-- 二法のLCMに互いに素な第三法を追加すると、周期はLCMと第三法の積になる。 -/
theorem refined_residue_constraints_iff {M d J : ℕ} (hcop : (M * d).Coprime J)
    {u v w c : ℤ} (hM : c ≡ u [ZMOD (M : ℤ)])
    (hd : c ≡ v [ZMOD (d : ℤ)]) (hJ : c ≡ w [ZMOD (J : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)] ∧
      x ≡ w [ZMOD (J : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d * J : ℤ)] := by
  have hL : (Nat.lcm M d).Coprime J :=
    hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
  rw [← and_assoc, residue_constraints_iff_lcm hM hd x,
    residue_constraints_iff_lcm (Int.ModEq.refl c) hJ x, hL.lcm_eq_mul]
  simp only [Nat.cast_mul]

/-- 正確なLCM周期の計数公式から、従来の誤差評価を直接導く。 -/
theorem compatible_residue_count_error (a b : ℤ) (hab : a ≤ b) {M d : ℕ}
    (hMpos : 0 < M) (hdpos : 0 < d) {u v c : ℤ}
    (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)]) :
    |((Finset.filter (fun x => x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)])
      (Finset.Ico a b)).card : ℝ) - ((b - a : ℤ) : ℝ) / Nat.lcm M d| ≤ 1 := by
  have hp : (0 : ℤ) < (Nat.lcm M d : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hMpos.ne' hdpos.ne')
  rw [compatible_residue_count_exact a b hMpos hdpos hM hd]
  exact residueIndexLength_absolute_error a b (Nat.lcm M d) c hab hp

end ArithLemmas.Mathlib.Int
