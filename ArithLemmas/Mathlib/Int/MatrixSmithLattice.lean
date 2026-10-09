module

public import ArithLemmas.Mathlib.ZMod.MatrixDiagonalReduction
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.StdBasis

/-!
# 任意の整数正方行列と法の合同格子の Smith 標準形

`A x ≡ b [ZMOD m]` を、`A` の列の整数像と `m ℤⁿ` の和で
生成された格子への所属問題に帰着させる。この格子は `m > 0` なら
必ず全ランクである。Mathlib の自由整数加群の Smith 標準形を
直接適用し、**任意の**正方整数行列について、有限個の整数の
整除条件で可解性を特徴付ける。

前段の `MatrixDiagonalReduction` と異なり、証明書の存在を
前提とせず、Mathlib の `Submodule.smithNormalFormOfRankEq` から
商格子の標準形を得る。ただし `U * A * V` 型の行列自体の
明示的な対角化を主張するものではない。
-/

public section

namespace ArithLemmas.Mathlib.Int

open ArithLemmas.Mathlib.ZMod

/-- 整数行列の像と法 `m` の整数倍を併せた有限指数合同格子。 -/
@[expose] def matrixCongruenceLattice (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℤ) :=
  (A.mulVecLin).range ⊔
    (LinearMap.lsmul ℤ (Fin n → ℤ) (m : ℤ)).range

/-- 格子への所属は `A x + m y = b` という整数等式と同値。 -/
theorem matrixCongruenceLattice_mem_iff (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) :
    b ∈ matrixCongruenceLattice n m A ↔
      ∃ x y : Fin n → ℤ, (fun i =>
        (integerMatrixForm n n A x) i + (m : ℤ) * y i) = b := by
  classical
  unfold matrixCongruenceLattice
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨u, ⟨x, rfl⟩, v, ⟨y, rfl⟩, h⟩
    refine ⟨x, y, ?_⟩
    funext i
    have hi := congrFun h i
    simpa only [Pi.add_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_apply_eq_sum, LinearMap.lsmul_apply,
      Pi.smul_apply, smul_eq_mul, integerMatrixForm] using hi
  · rintro ⟨x, y, h⟩
    refine ⟨A.mulVecLin x, ⟨x, rfl⟩,
      (LinearMap.lsmul ℤ (Fin n → ℤ) (m : ℤ)) y, ⟨y, rfl⟩, ?_⟩
    funext i
    have hi := congrFun h i
    simpa only [Pi.add_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_apply_eq_sum, LinearMap.lsmul_apply,
      Pi.smul_apply, smul_eq_mul, integerMatrixForm] using hi

/-- 整数行列の合同方程式は、付随する整数格子への所属問題と完全に同値。 -/
theorem integerMatrix_exists_iff_lattice_mem (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) :
    (∃ x : Fin n → ℤ,
      ∀ i, (integerMatrixForm n n A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      b ∈ matrixCongruenceLattice n m A := by
  classical
  rw [matrixCongruenceLattice_mem_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hh : ∀ i : Fin n, ∃ y : ℤ,
        b i - (integerMatrixForm n n A x) i = (m : ℤ) * y := by
      intro i
      obtain ⟨y, hy⟩ := Int.modEq_iff_dvd.mp (hx i)
      exact ⟨y, hy⟩
    choose y hy using hh
    refine ⟨x, y, ?_⟩
    funext i
    have hi := hy i
    omega
  · rintro ⟨x, y, h⟩
    refine ⟨x, fun i => Int.modEq_iff_dvd.mpr ?_⟩
    refine ⟨y i, ?_⟩
    have hi := congrFun h i
    omega

/-- `m > 0` の合同格子は全ランクである。 -/
theorem matrixCongruenceLattice_full_rank (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    Module.finrank ℤ (matrixCongruenceLattice n m A) =
      Module.finrank ℤ (Fin n → ℤ) := by
  classical
  let L := matrixCongruenceLattice n m A
  let t : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ) :=
    LinearMap.lsmul ℤ (Fin n → ℤ) (m : ℤ)
  have ht : ∀ x, t x ∈ L := by
    intro x
    exact Submodule.mem_sup_right ⟨x, rfl⟩
  have hinj : Function.Injective t :=
    LinearMap.lsmul_injective (by exact_mod_cast hm.ne')
  have hle : Module.finrank ℤ (Fin n → ℤ) ≤ Module.finrank ℤ L :=
    (t.codRestrict L ht).finrank_le_finrank_of_injective
      (hinj.codRestrict _)
  exact le_antisymm (Submodule.finrank_le L) hle

/-- 合同格子のSmith標準形における全空間の基底。 -/
noncomputable def matrixSmithBasis (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    Module.Basis (Fin n) ℤ (Fin n → ℤ) :=
  (matrixCongruenceLattice n m A).smithNormalFormTopBasis
    (Pi.basisFun ℤ (Fin n))
    (matrixCongruenceLattice_full_rank n m A hm)

/-- 合同格子のSmith標準形における整数対角係数。 -/
noncomputable def matrixSmithCoeff (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) : Fin n → ℤ :=
  (matrixCongruenceLattice n m A).smithNormalFormCoeffs
    (Pi.basisFun ℤ (Fin n)) (matrixCongruenceLattice_full_rank n m A hm)

/-- Smith標準形の係数はすべて非零。 -/
theorem matrixSmithCoeff_ne_zero (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) (i : Fin n) :
    matrixSmithCoeff n m A hm i ≠ 0 := by
  exact Submodule.smithNormalFormCoeffs_ne_zero
    (Pi.basisFun ℤ (Fin n)) (matrixCongruenceLattice_full_rank n m A hm) i

/-- 格子所属をSmith基底の各座標での割り切り条件に還元する。 -/
theorem matrixCongruenceLattice_mem_iff_smith_dvd (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m)
    (b : Fin n → ℤ) :
    b ∈ matrixCongruenceLattice n m A ↔
      ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
        (matrixSmithBasis n m A hm).repr b i := by
  classical
  let N := matrixCongruenceLattice n m A
  let bas := Pi.basisFun ℤ (Fin n)
  let h := matrixCongruenceLattice_full_rank n m A hm
  let a := N.smithNormalFormCoeffs bas h
  let bm := N.smithNormalFormTopBasis bas h
  let bn := N.smithNormalFormBotBasis bas h
  have hs : ∀ i, (bn i : Fin n → ℤ) = a i • bm i :=
    N.smithNormalFormBotBasis_def bas h
  change b ∈ N ↔ ∀ i, a i ∣ bm.repr b i
  simp_rw [bn.mem_submodule_iff', bn]
  have hrepr : ∀ (c : Fin n → ℤ) (i : Fin n),
      bm.repr (∑ j : Fin n, c j • a j • bm j) i = a i * c i := by
    intro c i
    simp only [← mul_smul, bm.repr_sum_self, mul_comm]
  have hsum (c : Fin n → ℤ) :
      (∑ j : Fin n, c j • (bn j : Fin n → ℤ)) =
        ∑ j : Fin n, c j • a j • bm j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j]
  constructor
  · rintro ⟨c, hc⟩ i
    rw [hc, hsum c]
    exact ⟨c i, hrepr c i⟩
  · intro hdvd
    choose c hc using hdvd
    refine ⟨c, ?_⟩
    have heq :
        bm.repr b =
          bm.repr (∑ j : Fin n, c j • a j • bm j) := by
      apply Finsupp.ext
      intro i
      calc
        (bm.repr b) i = a i * c i := hc i
        _ = (bm.repr (∑ j : Fin n, c j • a j • bm j)) i :=
          (hrepr c i).symm
    calc
      b = ∑ j : Fin n, c j • a j • bm j :=
        bm.repr.injective heq
      _ = ∑ j : Fin n, c j • (bn j : Fin n → ℤ) :=
        (hsum c).symm

/-- **任意**の正方整数行列について、Smith座標の割り切り条件は可解性と同値。 -/
theorem integerMatrix_exists_iff_smith_dvd (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (hm : 0 < m) :
    (∃ x : Fin n → ℤ,
      ∀ i, (integerMatrixForm n n A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
        (matrixSmithBasis n m A hm).repr b i := by
  exact (integerMatrix_exists_iff_lattice_mem n m A b).trans
    (matrixCongruenceLattice_mem_iff_smith_dvd n m A hm b)

/-- 合同格子の整数商を、Smith不変係数を法とする剰余群の直積に分解。 -/
noncomputable def matrixSmithQuotientEquiv (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    ((Fin n → ℤ) ⧸ matrixCongruenceLattice n m A) ≃+
      (∀ i : Fin n, ZMod (matrixSmithCoeff n m A hm i).natAbs) :=
  (matrixCongruenceLattice n m A).quotientEquivPiZMod
    (Pi.basisFun ℤ (Fin n)) (matrixCongruenceLattice_full_rank n m A hm)

/-- 商格子の指数（有限群の位数）はSmith不変係数の絶対値の積。 -/
theorem matrixSmithQuotient_card (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    Nat.card ((Fin n → ℤ) ⧸ matrixCongruenceLattice n m A) =
      ∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs := by
  classical
  rw [Nat.card_congr (matrixSmithQuotientEquiv n m A hm).toEquiv,
      Nat.card_pi]
  simp only [Nat.card_zmod]

end ArithLemmas.Mathlib.Int
