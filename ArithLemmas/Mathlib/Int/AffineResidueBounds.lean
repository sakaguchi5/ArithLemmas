module

public import ArithLemmas.Mathlib.Int.AffineResidue

/-!
# アフィン整数格子における長さと幅の評価（第4段階4E-4）

原典：`OAI/Combinatorics/Progressions/Lattices/ResidueSliceCountingCost.lean`。
4Bの誤差１の評価から、十分広い区間には指定合同類の点が
十分存在すること、出現点数が区間長を超えないことを導出する。
-/

public section

namespace ArithLemmas.Mathlib.Int

/-- 区間幅が `r * (B + 1)` 以上なら、その合同類の出現数は `B` 以上。 -/
theorem residueIndexLength_ge_of_width (a b r v : ℤ) (hr : 0 < r)
    (B : ℝ) (hB : 0 ≤ B)
    (hwidth : (r : ℝ) * (B + 1) ≤ ((b - a : ℤ) : ℝ)) :
    B ≤ (residueIndexLength a b r v : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hwidthpos : (0 : ℝ) < ((b - a : ℤ) : ℝ) :=
    (mul_pos hr' (by linarith : 0 < B + 1)).trans_le hwidth
  have hab : a ≤ b := by
    have h : (0 : ℤ) ≤ b - a := by exact_mod_cast hwidthpos.le
    omega
  have hlower := (abs_le.mp (residueIndexLength_absolute_error a b r v hab hr)).1
  have hratio : B + 1 ≤ ((b - a : ℤ) : ℝ) / (r : ℝ) :=
    (le_div_iff₀ hr').mpr (by simpa only [mul_comm] using hwidth)
  linarith

/-- 長さが公差の２倍以上の区間には、各合同類の点が存在する。 -/
theorem residueIndexLength_half_width (a v : ℤ) (N r : ℕ) (hr : 0 < r)
    (hwidth : 2 * (r : ℝ) ≤ (N : ℝ)) :
    0 < residueIndexLength a (a + N) r v ∧
      (N : ℝ) / 2 ≤ (r : ℝ) * (residueIndexLength a (a + N) r v : ℝ) := by
  have hrz : (0 : ℤ) < r := by exact_mod_cast hr
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hlength := residueIndexLength_ge_of_width a (a + N) r v hrz 1 (by norm_num)
    (by simpa only [add_sub_cancel_left, Int.cast_natCast] using
      (show (r : ℝ) * (1 + 1) ≤ (N : ℝ) by linarith))
  have herror := residueIndexLength_absolute_error a (a + N) r v (by omega) hrz
  simp only [add_sub_cancel_left, Int.cast_natCast] at herror
  have hlo := (abs_le.mp herror).1
  have hmul := mul_le_mul_of_nonneg_left hlo hrr.le
  have hdiv : (r : ℝ) * ((N : ℝ) / r) = (N : ℝ) := by field_simp
  refine ⟨?_, ?_⟩
  · exact_mod_cast
      (show (0 : ℝ) < (residueIndexLength a (a + N) r v : ℝ) by linarith)
  · nlinarith

/-- 合同類の整数点は区間全体の点数を超えない。 -/
theorem residueIndexLength_le_width (lo a : ℤ) (N M : ℕ) (hM : 0 < M) :
    residueIndexLength lo (lo + N) M a ≤ N := by
  rw [residueIndexLength_eq_card lo (lo + N) M a (Nat.cast_pos.mpr hM)]
  have h := Finset.card_filter_le (Finset.Ico lo (lo + N))
    (fun z => z ≡ a [ZMOD (M : ℤ)])
  simpa only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] using h

/-- 指定合同類が区間に現れるための幅に関する十分条件。 -/
theorem residueIndexLength_pos_of_width (a b r v : ℤ)
    (hr : 0 < r) (hwidth : (r : ℝ) * 2 ≤ ((b - a : ℤ) : ℝ)) :
    0 < residueIndexLength a b r v := by
  have hb := residueIndexLength_ge_of_width a b r v hr 1 (by norm_num)
    (by nlinarith [hwidth])
  have hcast : (0 : ℝ) < (residueIndexLength a b r v : ℝ) := by linarith
  exact_mod_cast hcast

end ArithLemmas.Mathlib.Int
