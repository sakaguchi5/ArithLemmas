module

public import ArithLemmas.Mathlib.Int.MatrixSmithConsequences
public import Mathlib.GroupTheory.Index

/-!
# Smith 合同格子の指数と任意の正方行列合同式の正確な解数

前段で得た有限指数格子 `A ℤⁿ + m ℤⁿ` と、法 `m` 上の
行列準同型の像を、座標ごとの整数剰余写像を通して接続する。
この接続によって Smith 不変係数の積は行列準同型の核の位数に
**厳密に一致**する。したがって可解な全ての右辺に対し、
解の個数を Smith 不変係数の積で与える。対角化証明書の仮定はない。
-/

public section

namespace ArithLemmas.Mathlib.Int

open ArithLemmas.Mathlib.ZMod

/-- 整数ベクトルを座標ごとに `ZMod m` へ還元する加法準同型。 -/
@[expose] def integerVectorModHom (n m : ℕ) :
    (Fin n → ℤ) →+ (Fin n → ZMod m) where
  toFun x := fun i => (x i : ZMod m)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp [Pi.add_apply]

/-- 正の法について整数ベクトルの剰余写像は全射。 -/
theorem integerVectorModHom_surjective (n m : ℕ) (hm : 0 < m) :
    Function.Surjective (integerVectorModHom n m) := by
  let : NeZero m := ⟨hm.ne'⟩
  intro y
  refine ⟨fun i => ((y i).val : ℤ), ?_⟩
  funext i
  change (((y i).val : ℤ) : ZMod m) = y i
  simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (y i)

/-- Smith 合同格子は、法 `m` の行列準同型の像の剰余写像による逆像。
任意の正方整数行列について成り立つ。 -/
theorem matrixCongruenceLattice_eq_comap_matrixRange (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    (matrixCongruenceLattice n m A).toAddSubgroup =
      (matrixModHom n n m A).range.comap (integerVectorModHom n m) := by
  ext b
  change (b ∈ matrixCongruenceLattice n m A) ↔
    ((fun i => (b i : ZMod m)) ∈ (matrixModHom n n m A).range)
  constructor
  · intro hb
    have hInt := (integerMatrix_exists_iff_lattice_mem n m A b).mpr hb
    have hMod := (integerMatrix_exists_iff_modFiber n n m A b hm).mp hInt
    exact (matrixModFiber_nonempty_iff_range n n m A _).mp hMod
  · intro hr
    have hMod := (matrixModFiber_nonempty_iff_range n n m A _).mpr hr
    have hInt := (integerMatrix_exists_iff_modFiber n n m A b hm).mpr hMod
    exact (integerMatrix_exists_iff_lattice_mem n m A b).mp hInt

/-- 法 `m` の行列の像の指数は、Smith 合同格子の指数と一致する。 -/
theorem matrixSmith_range_index_eq_lattice_index (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    (matrixModHom n n m A).range.index =
      (matrixCongruenceLattice n m A).toAddSubgroup.index := by
  calc
    (matrixModHom n n m A).range.index =
        ((matrixModHom n n m A).range.comap
          (integerVectorModHom n m)).index :=
      (AddSubgroup.index_comap_of_surjective
        (matrixModHom n n m A).range
        (integerVectorModHom_surjective n m hm)).symm
    _ = (matrixCongruenceLattice n m A).toAddSubgroup.index := by
      rw [← matrixCongruenceLattice_eq_comap_matrixRange n m A hm]

/-- 像の位数と Smith 商格子の位数との積は全剰余ベクトル数 `m^n`。
任意の行列に対して成立する、有限群版の格子指数公式。 -/
theorem matrixSmith_range_card_mul_quotient_card (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    Nat.card (matrixModHom n n m A).range *
      Nat.card ((Fin n → ℤ) ⧸ matrixCongruenceLattice n m A) = m ^ n := by
  let : NeZero m := ⟨hm.ne'⟩
  have hindex :
      Nat.card ((Fin n → ℤ) ⧸ matrixCongruenceLattice n m A) =
        (matrixCongruenceLattice n m A).toAddSubgroup.index := by
    change
      Nat.card ((Fin n → ℤ) ⧸
        (matrixCongruenceLattice n m A).toAddSubgroup) =
      (matrixCongruenceLattice n m A).toAddSubgroup.index
    exact (AddSubgroup.index_eq_card _).symm
  calc
    Nat.card (matrixModHom n n m A).range *
        Nat.card ((Fin n → ℤ) ⧸ matrixCongruenceLattice n m A) =
      Nat.card (matrixModHom n n m A).range *
        (matrixCongruenceLattice n m A).toAddSubgroup.index := by
          rw [hindex]
    _ = Nat.card (matrixModHom n n m A).range *
        (matrixModHom n n m A).range.index := by
          rw [matrixSmith_range_index_eq_lattice_index n m A hm]
    _ = Nat.card (Fin n → ZMod m) :=
      AddSubgroup.card_mul_index (matrixModHom n n m A).range
    _ = m ^ n := by
      simp [Nat.card_eq_fintype_card, ZMod.card]

/-- 像の位数と Smith 係数の絶対値の積の厳密な積公式。 -/
theorem matrixSmith_range_card_mul_coeff_prod (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    Nat.card (matrixModHom n n m A).range *
      (∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs) = m ^ n := by
  calc
    Nat.card (matrixModHom n n m A).range *
        (∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs) =
      Nat.card (matrixModHom n n m A).range *
        Nat.card ((Fin n → ℤ) ⧸ matrixCongruenceLattice n m A) := by
          rw [matrixSmithQuotient_card n m A hm]
    _ = m ^ n := matrixSmith_range_card_mul_quotient_card n m A hm

/-- **無条件の Smith 解数公式（核）**。
任意の正方整数行列の剰余核の位数は、格子の Smith 係数の絶対値の積。 -/
theorem matrixSmith_kernel_card_eq_coeff_prod (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    Nat.card (matrixModHom n n m A).ker =
      ∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs := by
  let p := Nat.card (matrixModHom n n m A).range
  have hprod := matrixSmith_range_card_mul_coeff_prod n m A hm
  have hkernel := matrixModHom_kernel_mul_range_card n n m A hm
  have hpos : 0 < p := by
    by_contra hp
    have hp0 : p = 0 := Nat.eq_zero_of_not_pos hp
    change p * (∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs) = m ^ n at hprod
    rw [hp0, zero_mul] at hprod
    have : 0 < m ^ n := pow_pos hm n
    omega
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    p * Nat.card (matrixModHom n n m A).ker = m ^ n := by
      simpa only [p, mul_comm] using hkernel
    _ = p * (∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs) :=
      hprod.symm

/-- **任意の正方行列に対する非空ファイバーの正確な解数**。
特別な対角化証明書を要求しない。 -/
theorem matrixSmith_fiber_card_eq_coeff_prod (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m)
    (b : Fin n → ZMod m)
    (hb : Nonempty (matrixModFiber n n m A b)) :
    Nat.card (matrixModFiber n n m A b) =
      ∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs := by
  obtain ⟨⟨c, hc⟩⟩ := hb
  calc
    Nat.card (matrixModFiber n n m A b) =
        Nat.card (matrixModHom n n m A).ker :=
      matrixModFiber_card_eq_kernel n n m A b c hc
    _ = _ := matrixSmith_kernel_card_eq_coeff_prod n m A hm

/-- 剰余ベクトルとして与えた右辺の Smith 可解性判定。 -/
theorem matrixSmith_modFiber_nonempty_iff_dvd (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m)
    (b : Fin n → ZMod m) :
    Nonempty (matrixModFiber n n m A b) ↔
      ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
        (matrixSmithBasis n m A hm).repr
          (fun j => ((b j).val : ℤ)) i := by
  let : NeZero m := ⟨hm.ne'⟩
  let bInt : Fin n → ℤ := fun j => ((b j).val : ℤ)
  have hcast : (fun j => (bInt j : ZMod m)) = b := by
    funext j
    change (((b j).val : ℤ) : ZMod m) = b j
    simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (b j)
  have h := (integerMatrix_exists_iff_modFiber n n m A bInt hm).symm.trans
    (integerMatrix_exists_iff_smith_dvd n m A bInt hm)
  simpa only [hcast, bInt] using h

/-- Smith 整除条件が成立しない右辺には解がない。 -/
theorem matrixSmith_fiber_card_zero_of_incompatible (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m)
    (b : Fin n → ZMod m)
    (hbad : ¬ ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
      (matrixSmithBasis n m A hm).repr
        (fun j => ((b j).val : ℤ)) i) :
    Nat.card (matrixModFiber n n m A b) = 0 := by
  have he : IsEmpty (matrixModFiber n n m A b) :=
    ⟨fun x => hbad ((matrixSmith_modFiber_nonempty_iff_dvd n m A hm b).mp ⟨x⟩)⟩
  let : IsEmpty (matrixModFiber n n m A b) := he
  let : Fintype (matrixModFiber n n m A b) := Fintype.ofIsEmpty
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_eq_zero_iff.mpr he

/-- 非空の場合は Smith 係数の積、非整合の場合は `0`。
この式は可解性・計数を一つの無条件等式に統合する。 -/
theorem matrixSmith_fiber_card_eq_ite (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m)
    (b : Fin n → ZMod m) :
    Nat.card (matrixModFiber n n m A b) =
      if ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
            (matrixSmithBasis n m A hm).repr
              (fun j => ((b j).val : ℤ)) i
      then ∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs
      else 0 := by
  classical
  by_cases h : ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
      (matrixSmithBasis n m A hm).repr (fun j => ((b j).val : ℤ)) i
  · rw [ite_eq_left h]
    exact matrixSmith_fiber_card_eq_coeff_prod n m A hm b
      ((matrixSmith_modFiber_nonempty_iff_dvd n m A hm b).mpr h)
  · rw [ite_eq_right h]
    exact matrixSmith_fiber_card_zero_of_incompatible n m A hm b h

end ArithLemmas.Mathlib.Int
