module

public import ArithLemmas.Mathlib.Int.RectangularSmithLattice
public import ArithLemmas.Mathlib.Int.MatrixSmithFiberCounting

/-!
# 任意の長方形整数行列の Smith 格子指数・核・正確な解数

`A : Matrix (Fin r) (Fin c) ℤ` と `m > 0` に対し、
`A ℤᶜ + m ℤʳ` の Smith 指数を `I` とすると、剰余写像の像の位数は
`m^r / I` であり、非空な各ファイバーの位数 `K` は
`K * m^r = m^c * I` を満たす。
これより任意の行数・列数（零次元も含む）について、
`K = (m^c * I) / m^r` という厳密な整数公式を得る。
-/

public section

namespace ArithLemmas.Mathlib.Int

open ArithLemmas.Mathlib.ZMod

/-- 長方形の Smith 合同格子は、剰余行列の像の整数剰余写像による逆像。 -/
theorem rectangularCongruenceLattice_eq_comap_matrixRange (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    (rectangularCongruenceLattice r c m A).toAddSubgroup =
      (matrixModHom r c m A).range.comap (integerVectorModHom r m) := by
  ext b
  change (b ∈ rectangularCongruenceLattice r c m A) ↔
    ((fun i => (b i : ZMod m)) ∈ (matrixModHom r c m A).range)
  constructor
  · intro hb
    have hInt := (rectangularIntegerMatrix_exists_iff_lattice_mem r c m A b).mpr hb
    have hMod := (integerMatrix_exists_iff_modFiber r c m A b hm).mp hInt
    exact (matrixModFiber_nonempty_iff_range r c m A _).mp hMod
  · intro hr
    have hMod := (matrixModFiber_nonempty_iff_range r c m A _).mpr hr
    have hInt := (integerMatrix_exists_iff_modFiber r c m A b hm).mpr hMod
    exact (rectangularIntegerMatrix_exists_iff_lattice_mem r c m A b).mp hInt

/-- 剰余行列の像の指数と長方形合同格子の指数の一致。 -/
theorem rectangularSmith_range_index_eq_lattice_index (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    (matrixModHom r c m A).range.index =
      (rectangularCongruenceLattice r c m A).toAddSubgroup.index := by
  calc
    (matrixModHom r c m A).range.index =
        ((matrixModHom r c m A).range.comap
          (integerVectorModHom r m)).index :=
      (AddSubgroup.index_comap_of_surjective
        (matrixModHom r c m A).range
        (integerVectorModHom_surjective r m hm)).symm
    _ = (rectangularCongruenceLattice r c m A).toAddSubgroup.index := by
      rw [← rectangularCongruenceLattice_eq_comap_matrixRange r c m A hm]

/-- 像の位数と合同格子の商の位数の積は全出力ベクトル数 `m^r`。 -/
theorem rectangularSmith_range_card_mul_quotient_card (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Nat.card (matrixModHom r c m A).range *
      Nat.card ((Fin r → ℤ) ⧸ rectangularCongruenceLattice r c m A) = m ^ r := by
  let : NeZero m := ⟨hm.ne'⟩
  have hindex :
      Nat.card ((Fin r → ℤ) ⧸ rectangularCongruenceLattice r c m A) =
        (rectangularCongruenceLattice r c m A).toAddSubgroup.index := by
    change
      Nat.card ((Fin r → ℤ) ⧸
        (rectangularCongruenceLattice r c m A).toAddSubgroup) =
      (rectangularCongruenceLattice r c m A).toAddSubgroup.index
    exact (AddSubgroup.index_eq_card _).symm
  calc
    Nat.card (matrixModHom r c m A).range *
        Nat.card ((Fin r → ℤ) ⧸ rectangularCongruenceLattice r c m A) =
      Nat.card (matrixModHom r c m A).range *
        (rectangularCongruenceLattice r c m A).toAddSubgroup.index := by
          rw [hindex]
    _ = Nat.card (matrixModHom r c m A).range *
        (matrixModHom r c m A).range.index := by
          rw [rectangularSmith_range_index_eq_lattice_index r c m A hm]
    _ = Nat.card (Fin r → ZMod m) :=
      AddSubgroup.card_mul_index (matrixModHom r c m A).range
    _ = m ^ r := by
      simp [Nat.card_eq_fintype_card, ZMod.card]

/-- 像の位数と Smith 係数の積の厳密な積公式。 -/
theorem rectangularSmith_range_card_mul_coeff_prod (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Nat.card (matrixModHom r c m A).range *
      (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs) = m ^ r := by
  calc
    Nat.card (matrixModHom r c m A).range *
        (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs) =
      Nat.card (matrixModHom r c m A).range *
        Nat.card ((Fin r → ℤ) ⧸ rectangularCongruenceLattice r c m A) := by
          rw [rectangularSmithQuotient_card r c m A hm]
    _ = m ^ r := rectangularSmith_range_card_mul_quotient_card r c m A hm

/-- **長方形Smith核指数公式**。
行数と列数の違いを保持したまま核の大きさを正確な積等式で表す。 -/
theorem rectangularSmith_kernel_card_mul_pow (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Nat.card (matrixModHom r c m A).ker * m ^ r =
      m ^ c * (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs) := by
  have hrange := rectangularSmith_range_card_mul_coeff_prod r c m A hm
  have hker := matrixModHom_kernel_mul_range_card r c m A hm
  calc
    Nat.card (matrixModHom r c m A).ker * m ^ r =
      Nat.card (matrixModHom r c m A).ker *
        (Nat.card (matrixModHom r c m A).range *
          (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs)) := by
        rw [hrange]
    _ = (Nat.card (matrixModHom r c m A).ker *
          Nat.card (matrixModHom r c m A).range) *
          (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs) := by
        ring
    _ = m ^ c *
          (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs) := by
        rw [hker]

/-- 任意の長方形行列の核の位数の除算による閉形式。 -/
theorem rectangularSmith_kernel_card_eq_div (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Nat.card (matrixModHom r c m A).ker =
      (m ^ c * (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs)) /
        m ^ r := by
  exact (Nat.div_eq_of_eq_mul_left (pow_pos hm r)
    (rectangularSmith_kernel_card_mul_pow r c m A hm).symm).symm

/-- 非空ファイバーの位数に対する整数積公式。 -/
theorem rectangularSmith_fiber_card_mul_pow (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m)
    (b : Fin r → ZMod m) (hb : Nonempty (matrixModFiber r c m A b)) :
    Nat.card (matrixModFiber r c m A b) * m ^ r =
      m ^ c * (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs) := by
  obtain ⟨⟨x, hx⟩⟩ := hb
  rw [matrixModFiber_card_eq_kernel r c m A b x hx]
  exact rectangularSmith_kernel_card_mul_pow r c m A hm

/-- **任意の長方形整数行列の非空ファイバーの正確な解数**。 -/
theorem rectangularSmith_fiber_card_eq_div (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m)
    (b : Fin r → ZMod m) (hb : Nonempty (matrixModFiber r c m A b)) :
    Nat.card (matrixModFiber r c m A b) =
      (m ^ c * (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs)) /
        m ^ r := by
  obtain ⟨⟨x, hx⟩⟩ := hb
  calc
    Nat.card (matrixModFiber r c m A b) =
        Nat.card (matrixModHom r c m A).ker :=
      matrixModFiber_card_eq_kernel r c m A b x hx
    _ = _ := rectangularSmith_kernel_card_eq_div r c m A hm

/-- 剰余ベクトルを右辺とする Smith 可解性判定。 -/
theorem rectangularSmith_modFiber_nonempty_iff_dvd (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m)
    (b : Fin r → ZMod m) :
    Nonempty (matrixModFiber r c m A b) ↔
      ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
        (rectangularSmithBasis r c m A hm).repr
          (fun j => ((b j).val : ℤ)) i := by
  let : NeZero m := ⟨hm.ne'⟩
  let bInt : Fin r → ℤ := fun j => ((b j).val : ℤ)
  have hcast : (fun j => (bInt j : ZMod m)) = b := by
    funext j
    change (((b j).val : ℤ) : ZMod m) = b j
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (b j)
  have h := (integerMatrix_exists_iff_modFiber r c m A bInt hm).symm.trans
    (rectangularIntegerMatrix_exists_iff_smith_dvd r c m A bInt hm)
  simpa only [hcast, bInt] using h

/-- 非整合な右辺には一つも解がない。 -/
theorem rectangularSmith_fiber_card_zero_of_incompatible (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m)
    (b : Fin r → ZMod m)
    (hbad : ¬ ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
      (rectangularSmithBasis r c m A hm).repr
        (fun j => ((b j).val : ℤ)) i) :
    Nat.card (matrixModFiber r c m A b) = 0 := by
  have he : IsEmpty (matrixModFiber r c m A b) :=
    ⟨fun x => hbad ((rectangularSmith_modFiber_nonempty_iff_dvd r c m A hm b).mp ⟨x⟩)⟩
  let : IsEmpty (matrixModFiber r c m A b) := he
  let : Fintype (matrixModFiber r c m A b) := Fintype.ofIsEmpty
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_eq_zero_iff.mpr he

/-- 可解性と解数を統合した無条件の Smith 計数公式。 -/
theorem rectangularSmith_fiber_card_eq_ite (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m)
    (b : Fin r → ZMod m) :
    Nat.card (matrixModFiber r c m A b) =
      if ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
          (rectangularSmithBasis r c m A hm).repr (fun j => ((b j).val : ℤ)) i
      then (m ^ c * (∏ i : Fin r,
          (rectangularSmithCoeff r c m A hm i).natAbs)) / m ^ r
      else 0 := by
  classical
  by_cases h : ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
      (rectangularSmithBasis r c m A hm).repr (fun j => ((b j).val : ℤ)) i
  · rw [ite_eq_left h]
    exact rectangularSmith_fiber_card_eq_div r c m A hm b
      ((rectangularSmith_modFiber_nonempty_iff_dvd r c m A hm b).mpr h)
  · rw [ite_eq_right h]
    exact rectangularSmith_fiber_card_zero_of_incompatible r c m A hm b h

end ArithLemmas.Mathlib.Int
