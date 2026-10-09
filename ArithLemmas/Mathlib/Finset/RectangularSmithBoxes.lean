module

public import ArithLemmas.Mathlib.Int.RectangularSmithCounting

/-!
# 長方形整数行列による格子箱の正確な解数

`A : Matrix (Fin r) (Fin c) ℤ` の解を、変数数 `c` の基本箱
`[0,m)^c` の整数点として数える。剰余ベクトル上の解ファイバーと
一対一に対応させ、Smith 格子指数による完全な計数公式を得る。
-/

public section

namespace ArithLemmas.Mathlib.Finset

open ArithLemmas.Mathlib.Int ArithLemmas.Mathlib.ZMod

/-- `c` 次元基本箱 `[0,m)^c` における `r` 本の合同式の整数点解。 -/
@[expose] def fundamentalRectangularCongruenceBox (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m) :=
  {x : Fin c → Fin m //
    matrixModForm r c m A (fun j => ((x j).val : ZMod m)) = b}

/-- 長方形基本箱の合同式の解集合は有限型。 -/
noncomputable instance (r c m : ℕ) (A : Matrix (Fin r) (Fin c) ℤ)
    (b : Fin r → ZMod m) :
    Fintype (fundamentalRectangularCongruenceBox r c m A b) := by
  classical
  unfold fundamentalRectangularCongruenceBox
  infer_instance

/-- 基本箱の整数点解と剰余行列合同式の解ファイバーの同値。 -/
noncomputable def fundamentalRectangularCongruenceBoxEquiv (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m)
    (hm : 0 < m) :
    fundamentalRectangularCongruenceBox r c m A b ≃
      matrixModFiber r c m A b := by
  letI : NeZero m := ⟨hm.ne'⟩
  classical
  refine {
    toFun := fun x => ⟨fun j => ((x.val j).val : ZMod m), x.property⟩
    invFun := fun y => ⟨fun j => ⟨(y.val j).val, (y.val j).val_lt⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · change matrixModForm r c m A
        (fun j => (((y.val j).val : ℕ) : ZMod m)) = b
    have hfun : (fun j => (((y.val j).val : ℕ) : ZMod m)) = y.val := by
      funext j
      exact ZMod.natCast_zmod_val (y.val j)
    rw [hfun]
    exact y.property
  · intro x
    apply Subtype.ext
    funext j
    apply Fin.ext
    exact ZMod.val_natCast_of_lt (x.val j).isLt
  · intro y
    apply Subtype.ext
    funext j
    exact ZMod.natCast_zmod_val (y.val j)

/-- 長方形基本箱の解が存在するための Smith 整除判定。 -/
theorem fundamentalRectangularCongruenceBox_nonempty_iff_smith_dvd (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m)
    (hm : 0 < m) :
    Nonempty (fundamentalRectangularCongruenceBox r c m A b) ↔
      ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
        (rectangularSmithBasis r c m A hm).repr
          (fun j => ((b j).val : ℤ)) i := by
  exact (Equiv.nonempty_congr
    (fundamentalRectangularCongruenceBoxEquiv r c m A b hm)).trans
      (rectangularSmith_modFiber_nonempty_iff_dvd r c m A hm b)

/-- 可解ならば基本箱内の解数は `m^c * Smith指数 / m^r`。 -/
theorem fundamentalRectangularCongruenceBox_card_eq_smith_div (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m)
    (hm : 0 < m)
    (hb : Nonempty (fundamentalRectangularCongruenceBox r c m A b)) :
    Fintype.card (fundamentalRectangularCongruenceBox r c m A b) =
      (m ^ c * (∏ i : Fin r, (rectangularSmithCoeff r c m A hm i).natAbs)) /
        m ^ r := by
  classical
  calc
    Fintype.card (fundamentalRectangularCongruenceBox r c m A b) =
        Nat.card (fundamentalRectangularCongruenceBox r c m A b) := by
          rw [Nat.card_eq_fintype_card]
    _ = Nat.card (matrixModFiber r c m A b) :=
      Nat.card_congr (fundamentalRectangularCongruenceBoxEquiv r c m A b hm)
    _ = _ := rectangularSmith_fiber_card_eq_div r c m A hm b
      ((Equiv.nonempty_congr
        (fundamentalRectangularCongruenceBoxEquiv r c m A b hm)).mp hb)

/-- Smith 整除条件が成り立たない場合、格子箱の解数は零。 -/
theorem fundamentalRectangularCongruenceBox_card_zero_of_incompatible (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m) (hm : 0 < m)
    (hbad : ¬ ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
      (rectangularSmithBasis r c m A hm).repr
        (fun j => ((b j).val : ℤ)) i) :
    Fintype.card (fundamentalRectangularCongruenceBox r c m A b) = 0 := by
  classical
  have he : IsEmpty (fundamentalRectangularCongruenceBox r c m A b) :=
    ⟨fun x => hbad ((fundamentalRectangularCongruenceBox_nonempty_iff_smith_dvd
      r c m A b hm).mp ⟨x⟩)⟩
  exact Fintype.card_eq_zero_iff.mpr he

/-- 長方形基本箱の解数を整合・非整合の両場合について与える完全公式。 -/
theorem fundamentalRectangularCongruenceBox_card_eq_ite (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m)
    (hm : 0 < m) :
    Fintype.card (fundamentalRectangularCongruenceBox r c m A b) =
      if ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
          (rectangularSmithBasis r c m A hm).repr (fun j => ((b j).val : ℤ)) i
      then (m ^ c * (∏ i : Fin r,
          (rectangularSmithCoeff r c m A hm i).natAbs)) / m ^ r
      else 0 := by
  classical
  by_cases h : ∀ i : Fin r, rectangularSmithCoeff r c m A hm i ∣
      (rectangularSmithBasis r c m A hm).repr (fun j => ((b j).val : ℤ)) i
  · rw [ite_eq_left h]
    exact fundamentalRectangularCongruenceBox_card_eq_smith_div r c m A b hm
      ((fundamentalRectangularCongruenceBox_nonempty_iff_smith_dvd r c m A b hm).mpr h)
  · rw [ite_eq_right h]
    exact fundamentalRectangularCongruenceBox_card_zero_of_incompatible r c m A b hm h

end ArithLemmas.Mathlib.Finset
