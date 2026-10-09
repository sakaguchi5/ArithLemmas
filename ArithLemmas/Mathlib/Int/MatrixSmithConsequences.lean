module

public import ArithLemmas.Mathlib.Int.MatrixSmithLattice
public import ArithLemmas.Mathlib.ZMod.MatrixCongruence
/-!
# 任意の行列合同式：Smith標準形の不変量と可解性の系

格子のSmith不変係数は全て正の法 `m` の約数（絶対値）となる。
商格子の位数は `m ^ n` を割る。可解性は右辺の剰余のみに依存し、
全剰余で可解となる条件は全不変係数の絶対値が `1` であること。
-/

public section

namespace ArithLemmas.Mathlib.Int

/-- 任意のSmith係数は、絶対値を取ると法を割る。 -/
theorem matrixSmithCoeff_natAbs_dvd_modulus (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m)
    (i : Fin n) :
    (matrixSmithCoeff n m A hm i).natAbs ∣ m := by
  classical
  let bas := matrixSmithBasis n m A hm
  have hin : (m : ℤ) • bas i ∈ matrixCongruenceLattice n m A := by
    change (m : ℤ) • bas i ∈
      (A.mulVecLin).range ⊔
        (LinearMap.lsmul ℤ (Fin n → ℤ) (m : ℤ)).range
    exact Submodule.mem_sup_right ⟨bas i, rfl⟩
  have hi := (matrixCongruenceLattice_mem_iff_smith_dvd n m A hm
    ((m : ℤ) • bas i)).mp hin i
  have hrepr : bas.repr ((m : ℤ) • bas i) i = (m : ℤ) := by
    rw [map_smul, Module.Basis.repr_self]
    simp
  rw [hrepr] at hi
  simpa using (Int.natAbs_dvd_natAbs.mpr hi)

/-- Smith格子の指数は法の `n` 乗の約数。 -/
theorem matrixSmithQuotient_card_dvd_pow (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    Nat.card ((Fin n → ℤ) ⧸ matrixCongruenceLattice n m A) ∣ m ^ n := by
  rw [matrixSmithQuotient_card n m A hm]
  have hd : (∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs) ∣
      ∏ _i : Fin n, m := by
    exact Finset.prod_dvd_prod_of_dvd _ _
      (fun i _ => matrixSmithCoeff_natAbs_dvd_modulus n m A hm i)
  simpa only [Finset.prod_const, Finset.card_fin] using hd

/-- 右辺が座標ごとに法 `m` に関して合同なら、Smith可解条件は変わらない。 -/
theorem matrixSmith_criterion_modEq_congr (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m)
    (b b' : Fin n → ℤ)
    (hbb' : ∀ i, b i ≡ b' i [ZMOD (m : ℤ)]) :
    (∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
      (matrixSmithBasis n m A hm).repr b i) ↔
    (∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
      (matrixSmithBasis n m A hm).repr b' i) := by
  rw [← integerMatrix_exists_iff_smith_dvd n m A b hm,
    ← integerMatrix_exists_iff_smith_dvd n m A b' hm]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i => (hx i).trans (hbb' i)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, fun i => (hx i).trans (hbb' i).symm⟩

/-- すべての右辺について可解であるための必要十分条件は、
Smith不変係数がすべて単元であること。 -/
theorem integerMatrix_surjective_iff_smith_units (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (hm : 0 < m) :
    (∀ b : Fin n → ℤ, ∃ x : Fin n → ℤ,
       ∀ i, (ZMod.integerMatrixForm n n A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      ∀ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs = 1 := by
  classical
  constructor
  · intro h i
    let bas := matrixSmithBasis n m A hm
    have hd : matrixSmithCoeff n m A hm i ∣ bas.repr (bas i) i :=
      (integerMatrix_exists_iff_smith_dvd n m A (bas i) hm).mp
        (h (bas i)) i
    have hd1 : matrixSmithCoeff n m A hm i ∣ (1 : ℤ) := by
      simpa only [Module.Basis.repr_self, Finsupp.single_eq_same] using hd
    have hdNat : (matrixSmithCoeff n m A hm i).natAbs ∣ (1 : ℕ) :=
      Int.natAbs_dvd_natAbs.mpr hd1
    exact Nat.dvd_one.mp hdNat
  · intro h b
    apply (integerMatrix_exists_iff_smith_dvd n m A b hm).mpr
    intro i
    apply Int.natAbs_dvd_natAbs.mp
    simp [h i]

end ArithLemmas.Mathlib.Int
