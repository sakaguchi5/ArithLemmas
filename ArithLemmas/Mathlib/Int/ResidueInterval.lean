module

public import Mathlib.Data.Int.CardIntervalMod
public import Mathlib.Basic.Real.Basic

/-!
# 整数区間の合同類計数（第4段階4B）

半開区間 `[a,b)` に入る指定合同類の個数を、区間長と法の比で評価する。
OpenAI 原典：`OAI/Combinatorics/Progressions/Lattices/ResidueSliceCountingCost.lean`。
Mathlib の `Int.Ico_filter_modEq_card` を出発点とし、汎用的な誤差評価だけを取り出す。
-/

public section

namespace ArithLemmas.Mathlib.Int

/-- 指定合同類の区間内出現回数を、区間長と法で上から評価する。 -/
theorem residue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤
      b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound :
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
        ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r =
          ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r =
      ((b - a : ℤ) : ℚ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

/-- 指定合同類の区間内出現回数は、区間長から法を引いた下界を満たす。 -/
theorem residue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ))
    (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound :
      ((b - a : ℤ) : ℚ) / r - 1 ≤
        ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r =
        ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r =
      ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

/-- 半開整数区間における指定合同類の個数と、期待値「幅／法」の誤差は１以下。 -/
theorem residue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := residue_card_mul_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast residue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r =
      ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  have huR :
      ((Finset.filter (fun x => x ≡ v [ZMOD r])
        (Finset.Ico a b)).card : ℝ) * (r : ℝ) ≤
          ((b - a : ℤ) : ℝ) + (r : ℝ) := by
    exact_mod_cast hu
  have hupper := (le_div_iff₀ hrR).mpr huR
  rw [add_div, div_self (ne_of_gt hrR)] at hupper
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- 整数区間の指定合同類の出現回数は、区間全体の要素数を超えない。 -/
theorem residue_card_le_interval (a b r v : ℤ) :
    (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card ≤
      (b - a).toNat := by
  simpa only [Int.card_Ico] using
    (Finset.card_filter_le (Finset.Ico a b) (fun x => x ≡ v [ZMOD r]))

end ArithLemmas.Mathlib.Int
