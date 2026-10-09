module

public import ArithLemmas.Mathlib.Int.MatrixSmithFiberCounting

/-!
# 任意の正方行列の周期基本箱における正確な計数

`Fin n → Fin m` を整数格子箱 `[0,m)^n` の標準剰余代表とみなす。
行列の合同条件を満たす格子点と `matrixModFiber` の同値を通じ、
Smith 標準形の係数積による計数公式を基本箱へ移す。
-/

public section

namespace ArithLemmas.Mathlib.Finset

open ArithLemmas.Mathlib.Int ArithLemmas.Mathlib.ZMod

/-- 整数基本箱 `[0,m)^n` 内の正方行列合同式の解集合。 -/
@[expose] def fundamentalMatrixCongruenceBox (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ZMod m) :=
  {x : Fin n → Fin m //
    matrixModForm n n m A (fun i => ((x i).val : ZMod m)) = b}

/-- 基本箱内の解集合は有限。 -/
noncomputable instance (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ZMod m) :
    Fintype (fundamentalMatrixCongruenceBox n m A b) := by
  classical
  unfold fundamentalMatrixCongruenceBox
  infer_instance

/-- 基本箱の格子点解と剰余ベクトル解を一対一に対応させる。 -/
noncomputable def fundamentalMatrixCongruenceBoxEquiv (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ZMod m)
    (hm : 0 < m) :
    fundamentalMatrixCongruenceBox n m A b ≃
      matrixModFiber n n m A b := by
  letI : NeZero m := ⟨hm.ne'⟩
  classical
  refine {
    toFun := fun x => ⟨fun i => ((x.val i).val : ZMod m), x.property⟩
    invFun := fun y => ⟨fun i => ⟨(y.val i).val, (y.val i).val_lt⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · change matrixModForm n n m A
        (fun i => (((y.val i).val : ℕ) : ZMod m)) = b
    have hfun : (fun i => (((y.val i).val : ℕ) : ZMod m)) = y.val := by
      funext i
      exact ZMod.natCast_zmod_val (y.val i)
    rw [hfun]
    exact y.property
  · intro x
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (x.val i).isLt
  · intro y
    apply Subtype.ext
    funext i
    exact ZMod.natCast_zmod_val (y.val i)

/-- 整数基本箱に解が存在することのSmith座標による必要十分条件。 -/
theorem fundamentalMatrixCongruenceBox_nonempty_iff_smith_dvd (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ZMod m)
    (hm : 0 < m) :
    Nonempty (fundamentalMatrixCongruenceBox n m A b) ↔
      ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
        (matrixSmithBasis n m A hm).repr
          (fun j => ((b j).val : ℤ)) i := by
  exact (Equiv.nonempty_congr
    (fundamentalMatrixCongruenceBoxEquiv n m A b hm)).trans
      (matrixSmith_modFiber_nonempty_iff_dvd n m A hm b)

/-- 可解な場合の基本箱の解数は、Smith係数の絶対値の積と厳密に一致。 -/
theorem fundamentalMatrixCongruenceBox_card_eq_smith_prod (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ZMod m)
    (hm : 0 < m)
    (hb : Nonempty (fundamentalMatrixCongruenceBox n m A b)) :
    Fintype.card (fundamentalMatrixCongruenceBox n m A b) =
      ∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs := by
  classical
  calc
    Fintype.card (fundamentalMatrixCongruenceBox n m A b) =
        Nat.card (fundamentalMatrixCongruenceBox n m A b) := by
          rw [Nat.card_eq_fintype_card]
    _ = Nat.card (matrixModFiber n n m A b) :=
      Nat.card_congr (fundamentalMatrixCongruenceBoxEquiv n m A b hm)
    _ = ∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs :=
      matrixSmith_fiber_card_eq_coeff_prod n m A hm b
        ((Equiv.nonempty_congr
          (fundamentalMatrixCongruenceBoxEquiv n m A b hm)).mp hb)

/-- 右辺がSmith条件に不整合なら、基本箱の解数は `0`。 -/
theorem fundamentalMatrixCongruenceBox_card_zero_of_incompatible (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ZMod m)
    (hm : 0 < m)
    (hbad : ¬ ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
      (matrixSmithBasis n m A hm).repr
        (fun j => ((b j).val : ℤ)) i) :
    Fintype.card (fundamentalMatrixCongruenceBox n m A b) = 0 := by
  classical
  have he : IsEmpty (fundamentalMatrixCongruenceBox n m A b) :=
    ⟨fun x => hbad ((fundamentalMatrixCongruenceBox_nonempty_iff_smith_dvd
      n m A b hm).mp ⟨x⟩)⟩
  exact Fintype.card_eq_zero_iff.mpr he

/-- **任意の正方整数行列**について、基本箱での解数を条件分岐なしの
仮定でなく `if` で表した完全な計数公式。 -/
theorem fundamentalMatrixCongruenceBox_card_eq_ite (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ZMod m)
    (hm : 0 < m) :
    Fintype.card (fundamentalMatrixCongruenceBox n m A b) =
      if ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
            (matrixSmithBasis n m A hm).repr
              (fun j => ((b j).val : ℤ)) i
      then ∏ i : Fin n, (matrixSmithCoeff n m A hm i).natAbs
      else 0 := by
  classical
  by_cases h : ∀ i : Fin n, matrixSmithCoeff n m A hm i ∣
      (matrixSmithBasis n m A hm).repr (fun j => ((b j).val : ℤ)) i
  · rw [ite_eq_left h]
    exact fundamentalMatrixCongruenceBox_card_eq_smith_prod n m A b hm
      ((fundamentalMatrixCongruenceBox_nonempty_iff_smith_dvd n m A b hm).mpr h)
  · rw [ite_eq_right h]
    exact fundamentalMatrixCongruenceBox_card_zero_of_incompatible n m A b hm h

end ArithLemmas.Mathlib.Finset
