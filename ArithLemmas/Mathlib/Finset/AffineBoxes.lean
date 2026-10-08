module

public import ArithLemmas.Mathlib.Int.AffineResidueBounds
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# 独立な整数区間・合同類からなるアフィン格子箱（第4段階4E-4）

各座標に整数半開区間と合同類条件を指定した直積を有限集合として扱う。
原典 `OAI/Combinatorics/Progressions/Lattices/ResidueSliceCountingCost.lean`
の１次元アフィン添字を多次元に適用する派生定理。
-/

public section

namespace ArithLemmas.Mathlib.Finset

open ArithLemmas.Mathlib.Int

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- 各座標が半開区間内の指定合同類に属する有限整数格子箱。 -/
noncomputable def affineResidueBox (a b r v : ι → ℤ) : Finset (ι → ℤ) := by
  classical
  exact Fintype.piFinset (fun i =>
    (Finset.Ico (a i) (b i)).filter (fun x => x ≡ v i [ZMOD r i]))

/-- 格子箱への所属を座標ごとの上下界・合同条件へ分解する。 -/
@[simp] theorem mem_affineResidueBox (a b r v : ι → ℤ) (x : ι → ℤ) :
    x ∈ affineResidueBox a b r v ↔
      ∀ i, a i ≤ x i ∧ x i < b i ∧ x i ≡ v i [ZMOD r i] := by
  classical
  simp [affineResidueBox, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_Ico,
    and_assoc]

/-- 独立な各座標のアフィン添字長の積が格子箱内の整数点数に等しい。 -/
theorem card_affineResidueBox (a b r v : ι → ℤ) (hr : ∀ i, 0 < r i) :
    (affineResidueBox a b r v).card =
      ∏ i : ι, residueIndexLength (a i) (b i) (r i) (v i) := by
  classical
  unfold affineResidueBox
  rw [Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro i hi
  exact (residueIndexLength_eq_card (a i) (b i) (r i) (v i) (hr i)).symm

/-- 全座標のアフィン添字長が一定なら、格子点数はその長さの次元冪。 -/
theorem card_affineResidueBox_uniform (d L : ℕ)
    (a b r v : Fin d → ℤ) (hr : ∀ i, 0 < r i)
    (hL : ∀ i, residueIndexLength (a i) (b i) (r i) (v i) = L) :
    (affineResidueBox a b r v).card = L ^ d := by
  rw [card_affineResidueBox a b r v hr]
  simp [hL]

/-- 各座標の区間幅が公差２周期以上なら、指定剰余の格子箱は非空。 -/
theorem affineResidueBox_nonempty_of_width (a b r v : ι → ℤ)
    (hr : ∀ i, 0 < r i)
    (hw : ∀ i, (r i : ℝ) * 2 ≤ (((b i - a i : ℤ) : ℝ))) :
    (affineResidueBox a b r v).Nonempty := by
  classical
  have hi (i : ι) : 0 < residueIndexLength (a i) (b i) (r i) (v i) :=
    residueIndexLength_pos_of_width (a i) (b i) (r i) (v i) (hr i) (hw i)
  have hcard : 0 < (affineResidueBox a b r v).card := by
    rw [card_affineResidueBox a b r v hr]
    exact Finset.prod_pos (fun i _ => hi i)
  exact Finset.card_pos.mp hcard

end ArithLemmas.Mathlib.Finset
