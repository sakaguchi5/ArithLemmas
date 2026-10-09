module

public import ArithLemmas.Mathlib.Int.MatrixSmithLattice

/-!
# 長方形整数行列の合同格子と Smith 不変量

`A : Matrix (Fin r) (Fin c) ℤ` に対して、像格子と `m ℤʳ` の和を扱う。
列数 `c` に制限はなく、`r = 0`、`c = 0` も含む。
`m > 0` の場合、この格子は必ず全ランクであるため、Mathlib の
部分加群 Smith 標準形により任意の長方形行列の可解性判定を得る。
-/

public section

namespace ArithLemmas.Mathlib.Int

open ArithLemmas.Mathlib.ZMod

/-- 長方形行列 `A` と法 `m` が定める整数の合同格子。 -/
@[expose] def rectangularCongruenceLattice (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) : Submodule ℤ (Fin r → ℤ) :=
  A.mulVecLin.range ⊔
    (LinearMap.lsmul ℤ (Fin r → ℤ) (m : ℤ)).range

/-- 合同格子の所属を二つの整数ベクトルの存在で表す。 -/
theorem rectangularCongruenceLattice_mem_iff (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ℤ) :
    b ∈ rectangularCongruenceLattice r c m A ↔
      ∃ x : Fin c → ℤ, ∃ y : Fin r → ℤ,
        (fun i => (integerMatrixForm r c A x) i + (m : ℤ) * y i) = b := by
  classical
  unfold rectangularCongruenceLattice
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
      (LinearMap.lsmul ℤ (Fin r → ℤ) (m : ℤ)) y, ⟨y, rfl⟩, ?_⟩
    funext i
    have hi := congrFun h i
    simpa only [Pi.add_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_apply_eq_sum, LinearMap.lsmul_apply,
      Pi.smul_apply, smul_eq_mul, integerMatrixForm] using hi

/-- 任意の長方形整数行列の合同式の可解性と格子所属は同値。 -/
theorem rectangularIntegerMatrix_exists_iff_lattice_mem (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ℤ) :
    (∃ x : Fin c → ℤ,
      ∀ i, (integerMatrixForm r c A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      b ∈ rectangularCongruenceLattice r c m A := by
  classical
  rw [rectangularCongruenceLattice_mem_iff]
  constructor
  · rintro ⟨x, hx⟩
    have hh : ∀ i : Fin r, ∃ y : ℤ,
        b i - (integerMatrixForm r c A x) i = (m : ℤ) * y := by
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

/-- 正の法の長方形合同格子は行数に等しい階数を持つ。 -/
theorem rectangularCongruenceLattice_full_rank (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Module.finrank ℤ (rectangularCongruenceLattice r c m A) =
      Module.finrank ℤ (Fin r → ℤ) := by
  classical
  let L := rectangularCongruenceLattice r c m A
  let t : (Fin r → ℤ) →ₗ[ℤ] (Fin r → ℤ) :=
    LinearMap.lsmul ℤ (Fin r → ℤ) (m : ℤ)
  have ht : ∀ x, t x ∈ L := by
    intro x
    exact Submodule.mem_sup_right ⟨x, rfl⟩
  have hinj : Function.Injective t :=
    LinearMap.lsmul_injective (by exact_mod_cast hm.ne')
  have hle : Module.finrank ℤ (Fin r → ℤ) ≤ Module.finrank ℤ L :=
    (t.codRestrict L ht).finrank_le_finrank_of_injective
      (hinj.codRestrict _)
  exact le_antisymm (Submodule.finrank_le L) hle

/-- 長方形合同格子に対する Smith 基底（出力空間の基底）。 -/
noncomputable def rectangularSmithBasis (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Module.Basis (Fin r) ℤ (Fin r → ℤ) :=
  (rectangularCongruenceLattice r c m A).smithNormalFormTopBasis
    (Pi.basisFun ℤ (Fin r))
    (rectangularCongruenceLattice_full_rank r c m A hm)

/-- 長方形合同格子の Smith 対角係数は行数 `r` 個。 -/
noncomputable def rectangularSmithCoeff (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) : Fin r → ℤ :=
  (rectangularCongruenceLattice r c m A).smithNormalFormCoeffs
    (Pi.basisFun ℤ (Fin r))
    (rectangularCongruenceLattice_full_rank r c m A hm)

/-- 正の法を含むため Smith 係数は全て非零。 -/
theorem rectangularSmithCoeff_ne_zero (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) (i : Fin r) :
    rectangularSmithCoeff r c m A hm i ≠ 0 := by
  exact Submodule.smithNormalFormCoeffs_ne_zero
    (Pi.basisFun ℤ (Fin r)) (rectangularCongruenceLattice_full_rank r c m A hm) i

/-- 任意の長方形合同格子について Smith 座標による完全な所属判定。 -/
theorem rectangularCongruenceLattice_mem_iff_smith_dvd (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) (b : Fin r → ℤ) :
    b ∈ rectangularCongruenceLattice r c m A ↔
      ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
        (rectangularSmithBasis r c m A hm).repr b i := by
  classical
  let N := rectangularCongruenceLattice r c m A
  let bas := Pi.basisFun ℤ (Fin r)
  let h := rectangularCongruenceLattice_full_rank r c m A hm
  let a := N.smithNormalFormCoeffs bas h
  let bm := N.smithNormalFormTopBasis bas h
  let bn := N.smithNormalFormBotBasis bas h
  have hs : ∀ i, (bn i : Fin r → ℤ) = a i • bm i :=
    N.smithNormalFormBotBasis_def bas h
  change b ∈ N ↔ ∀ i, a i ∣ bm.repr b i
  simp_rw [bn.mem_submodule_iff', bn]
  have hrepr : ∀ (d : Fin r → ℤ) (i : Fin r),
      bm.repr (∑ j : Fin r, d j • a j • bm j) i = a i * d i := by
    intro d i
    simp only [← mul_smul, bm.repr_sum_self, mul_comm]
  have hsum (d : Fin r → ℤ) :
      (∑ j : Fin r, d j • (bn j : Fin r → ℤ)) =
        ∑ j : Fin r, d j • a j • bm j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hs j]
  constructor
  · rintro ⟨d, hd⟩ i
    rw [hd, hsum d]
    exact ⟨d i, hrepr d i⟩
  · intro hdvd
    choose d hd using hdvd
    refine ⟨d, ?_⟩
    have heq :
        bm.repr b =
          bm.repr (∑ j : Fin r, d j • a j • bm j) := by
      apply Finsupp.ext
      intro i
      calc
        (bm.repr b) i = a i * d i := hd i
        _ = (bm.repr (∑ j : Fin r, d j • a j • bm j)) i :=
          (hrepr d i).symm
    calc
      b = ∑ j : Fin r, d j • a j • bm j :=
        bm.repr.injective heq
      _ = ∑ j : Fin r, d j • (bn j : Fin r → ℤ) :=
        (hsum d).symm

/-- 行数・列数が独立した任意の整数行列の Smith 可解性判定。 -/
theorem rectangularIntegerMatrix_exists_iff_smith_dvd (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ℤ) (hm : 0 < m) :
    (∃ x : Fin c → ℤ,
      ∀ i, (integerMatrixForm r c A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
        (rectangularSmithBasis r c m A hm).repr b i := by
  exact (rectangularIntegerMatrix_exists_iff_lattice_mem r c m A b).trans
    (rectangularCongruenceLattice_mem_iff_smith_dvd r c m A hm b)

/-- 商格子の構造：行数個の巡回群への非計算的同値。 -/
noncomputable def rectangularSmithQuotientEquiv (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    ((Fin r → ℤ) ⧸ rectangularCongruenceLattice r c m A) ≃+
      (∀ i : Fin r, ZMod (rectangularSmithCoeff r c m A hm i).natAbs) :=
  (rectangularCongruenceLattice r c m A).quotientEquivPiZMod
    (Pi.basisFun ℤ (Fin r)) (rectangularCongruenceLattice_full_rank r c m A hm)

/-- 長方形合同格子の指数は Smith 係数の絶対値の積。 -/
theorem rectangularSmithQuotient_card (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Nat.card ((Fin r → ℤ) ⧸ rectangularCongruenceLattice r c m A) =
      ∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs := by
  classical
  rw [Nat.card_congr (rectangularSmithQuotientEquiv r c m A hm).toEquiv, Nat.card_pi]
  simp only [Nat.card_zmod]

/-- 各 Smith 係数の絶対値は法 `m` の約数。 -/
theorem rectangularSmithCoeff_natAbs_dvd_modulus (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) (i : Fin r) :
    (rectangularSmithCoeff r c m A hm i).natAbs ∣ m := by
  classical
  let bas := rectangularSmithBasis r c m A hm
  have hin : (m : ℤ) • bas i ∈ rectangularCongruenceLattice r c m A := by
    change (m : ℤ) • bas i ∈
      (A.mulVecLin).range ⊔
        (LinearMap.lsmul ℤ (Fin r → ℤ) (m : ℤ)).range
    exact Submodule.mem_sup_right ⟨bas i, rfl⟩
  have hi := (rectangularCongruenceLattice_mem_iff_smith_dvd r c m A hm
    ((m : ℤ) • bas i)).mp hin i
  have hrepr : bas.repr ((m : ℤ) • bas i) i = (m : ℤ) := by
    rw [map_smul, Module.Basis.repr_self]
    simp
  rw [hrepr] at hi
  simpa using (Int.natAbs_dvd_natAbs.mpr hi)

/-- 商格子の指数は `m^r` を割り切る。 -/
theorem rectangularSmithQuotient_card_dvd_pow (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Nat.card ((Fin r → ℤ) ⧸ rectangularCongruenceLattice r c m A) ∣ m ^ r := by
  rw [rectangularSmithQuotient_card r c m A hm]
  have hd : (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs) ∣
      ∏ _i : Fin r, m := by
    exact Finset.prod_dvd_prod_of_dvd _ _
      (fun i _ => rectangularSmithCoeff_natAbs_dvd_modulus r c m A hm i)
  simpa only [Finset.prod_const, Finset.card_fin] using hd


/-- 任意の長方形整数行列がすべての剰余右辺を実現するための必要十分条件。 -/
theorem rectangularIntegerMatrix_surjective_iff_smith_units (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    (∀ b : Fin r → ℤ, ∃ x : Fin c → ℤ,
        ∀ i, (integerMatrixForm r c A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      ∀ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs = 1 := by
  classical
  constructor
  · intro h i
    let bas := rectangularSmithBasis r c m A hm
    have hd : rectangularSmithCoeff r c m A hm i ∣ bas.repr (bas i) i :=
      (rectangularIntegerMatrix_exists_iff_smith_dvd r c m A (bas i) hm).mp
        (h (bas i)) i
    have hd1 : rectangularSmithCoeff r c m A hm i ∣ (1 : ℤ) := by
      simpa only [Module.Basis.repr_self, Finsupp.single_eq_same] using hd
    have hdNat : (rectangularSmithCoeff r c m A hm i).natAbs ∣ (1 : ℕ) :=
      Int.natAbs_dvd_natAbs.mpr hd1
    exact Nat.dvd_one.mp hdNat
  · intro h b
    apply (rectangularIntegerMatrix_exists_iff_smith_dvd r c m A b hm).mpr
    intro i
    apply Int.natAbs_dvd_natAbs.mp
    simp [h i]

/-- 正方行列に制限したとき、長方形版と既存の Smith 格子の指数は一致する。
Smith 基底の選択に依存しない数値不変量であることも示す。 -/
theorem rectangularSmithQuotient_card_eq_square (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    (∏ i : Fin n, (rectangularSmithCoeff n n m A hm i).natAbs) =
      ∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs := by
  rw [← rectangularSmithQuotient_card n n m A hm,
      ← matrixSmithQuotient_card n m A hm]
  rfl

end ArithLemmas.Mathlib.Int
