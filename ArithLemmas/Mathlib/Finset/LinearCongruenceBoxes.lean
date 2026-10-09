module

public import ArithLemmas.Mathlib.ZMod.LinearCongruenceFibers
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# 多変数一次合同式の基本格子箱における正確な計数

`Fin d → Fin m` を整数格子の基本箱 `[0,m)^d` とみなし、
座標ごとの整数剰余の代表から `ZMod m` 上の解集合への同値を構成する。
これにより、GCD による可解性条件、核の大きさによる正確な個数、
および核と像の積による計数公式を得る。
-/

public section

namespace ArithLemmas.Mathlib.Finset

open ArithLemmas.Mathlib.Int ArithLemmas.Mathlib.ZMod

/-- 整数基本箱 `[0,m)^d` における一つの線形合同条件の解。 -/
@[expose] def fundamentalLinearCongruenceBox (d m : ℕ) (a : Fin d → ℤ)
    (b : ZMod m) :=
  {x : Fin d → Fin m //
    (∑ i : Fin d, (a i : ZMod m) * ((x i).val : ZMod m)) = b}

/-- 基本箱の合同解集合は有限型である。 -/
noncomputable instance (d m : ℕ) (a : Fin d → ℤ)
    (b : ZMod m) :
    Fintype (fundamentalLinearCongruenceBox d m a b) := by
  classical
  unfold fundamentalLinearCongruenceBox
  infer_instance

/-- 基本箱の剰余代表と `ZMod m` 上の解集合は自然に同値。 -/
noncomputable def fundamentalLinearCongruenceBoxEquiv
    (d m : ℕ) (a : Fin d → ℤ) (b : ZMod m) (hm : 0 < m) :
    fundamentalLinearCongruenceBox d m a b ≃
      modLinearFiber d m a b := by
  letI : NeZero m := ⟨hm.ne'⟩
  classical
  refine {
    toFun := fun x => ⟨fun i => ((x.val i).val : ZMod m), x.property⟩
    invFun := fun y => ⟨fun i => ⟨(y.val i).val, (y.val i).val_lt⟩, ?_⟩
    left_inv := ?_
    right_inv := ?_
  }
  · change modLinearForm d m a
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

/-- 基本箱に解が存在するための必要十分条件は GCD 整除性。 -/
theorem fundamentalLinearCongruenceBox_nonempty_iff_gcd_dvd
    (d m : ℕ) (a : Fin d → ℤ) (b : ℤ) (hm : 0 < m) :
    Nonempty (fundamentalLinearCongruenceBox d m a (b : ZMod m)) ↔
      (multivariableLinearGCD (Finset.univ : Finset (Fin d)) a m : ℤ) ∣ b := by
  exact (Equiv.nonempty_congr
    (fundamentalLinearCongruenceBoxEquiv d m a (b : ZMod m) hm)).trans
      (modLinearFiber_nonempty_iff_gcd_dvd d m a b hm)

/-- 基本箱の非空な合同解集合は、加法群準同型の核と同じ点数を持つ。 -/
theorem fundamentalLinearCongruenceBox_card_eq_kernel_card
    (d m : ℕ) (a : Fin d → ℤ) (b : ZMod m) (hm : 0 < m)
    (c : Fin d → Fin m)
    (hc : (∑ i : Fin d, (a i : ZMod m) * ((c i).val : ZMod m)) = b) :
    Fintype.card (fundamentalLinearCongruenceBox d m a b) =
      Nat.card (modLinearHom d m a).ker := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  calc
    Fintype.card (fundamentalLinearCongruenceBox d m a b) =
        Nat.card (fundamentalLinearCongruenceBox d m a b) := by
      rw [Nat.card_eq_fintype_card]
    _ = Nat.card (modLinearFiber d m a b) :=
      Nat.card_congr (fundamentalLinearCongruenceBoxEquiv d m a b hm)
    _ = Nat.card (modLinearHom d m a).ker :=
      modLinearFiber_card_eq_kernel_card d m a b hm
        (fun i => ((c i).val : ZMod m)) hc

/-- 非空基本箱で、解数と像の位数の積は正確に `m^d`。 -/
theorem fundamentalLinearCongruenceBox_card_mul_range
    (d m : ℕ) (a : Fin d → ℤ) (b : ZMod m) (hm : 0 < m)
    (c : Fin d → Fin m)
    (hc : (∑ i : Fin d, (a i : ZMod m) * ((c i).val : ZMod m)) = b) :
    Fintype.card (fundamentalLinearCongruenceBox d m a b) *
      Nat.card (modLinearHom d m a).range = m ^ d := by
  rw [fundamentalLinearCongruenceBox_card_eq_kernel_card d m a b hm c hc]
  exact modLinearHom_kernel_mul_range_card d m a hm

/-- GCD 障害がある場合、整数基本箱には一つも解がない。 -/
theorem fundamentalLinearCongruenceBox_card_zero_of_not_gcd_dvd
    (d m : ℕ) (a : Fin d → ℤ) (b : ℤ) (hm : 0 < m)
    (hbad : ¬ (multivariableLinearGCD
      (Finset.univ : Finset (Fin d)) a m : ℤ) ∣ b) :
    Fintype.card (fundamentalLinearCongruenceBox d m a (b : ZMod m)) = 0 := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  have he : IsEmpty (fundamentalLinearCongruenceBox d m a (b : ZMod m)) :=
    ⟨fun x => hbad ((fundamentalLinearCongruenceBox_nonempty_iff_gcd_dvd
      d m a b hm).mp ⟨x⟩)⟩
  exact Fintype.card_eq_zero_iff.mpr he


/-- 少なくとも一座標がある基本格子箱での、GCD を用いた解数の閉形式。 -/
theorem fundamentalLinearCongruenceBox_card_closed_succ
    (d m : ℕ) (a : Fin (d + 1) → ℤ) (b : ZMod m) (hm : 0 < m)
    (c : Fin (d + 1) → Fin m)
    (hc : (∑ i : Fin (d + 1),
      (a i : ZMod m) * ((c i).val : ZMod m)) = b) :
    Fintype.card (fundamentalLinearCongruenceBox (d + 1) m a b) =
      multivariableLinearGCD
        (Finset.univ : Finset (Fin (d + 1))) a m * m ^ d := by
  have hcount := fundamentalLinearCongruenceBox_card_eq_kernel_card
    (d + 1) m a b hm c hc
  rw [hcount]
  have hclosed := modLinearFiber_card_closed_succ (d := d) (m := m)
    a b hm (fun i => ((c i).val : ZMod m)) hc
  rw [modLinearFiber_card_eq_kernel_card
    (d + 1) m a b hm (fun i => ((c i).val : ZMod m)) hc] at hclosed
  exact hclosed

/-- 各座標を `(周期番号, 法 `m` の剰余)` で表した、辺長 `t*m` の格子箱。 -/
@[expose] def periodicLinearCongruenceBox (d t m : ℕ) (a : Fin d → ℤ)
    (b : ZMod m) :=
  {x : Fin d → Fin t × Fin m //
    (∑ i : Fin d, (a i : ZMod m) * ((x i).2.val : ZMod m)) = b}

/-- 周期箱の合同解集合は有限型である。 -/
noncomputable instance (d t m : ℕ) (a : Fin d → ℤ)
    (b : ZMod m) :
    Fintype (periodicLinearCongruenceBox d t m a b) := by
  classical
  unfold periodicLinearCongruenceBox
  infer_instance

/-- 周期番号は合同制約と独立なので、解空間は周期番号と基本箱の直積。 -/
noncomputable def periodicLinearCongruenceBoxEquiv
    (d t m : ℕ) (a : Fin d → ℤ) (b : ZMod m) :
    periodicLinearCongruenceBox d t m a b ≃
      (Fin d → Fin t) × fundamentalLinearCongruenceBox d m a b where
  toFun x :=
    (fun i => (x.val i).1, ⟨fun i => (x.val i).2, x.property⟩)
  invFun y :=
    ⟨fun i => (y.1 i, y.2.val i), y.2.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact Prod.mk.eta
  right_inv y := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      rfl

/-- 辺長 `t*m` の `d+1` 次元周期箱では、正確な解数は
`t^(d+1) * gcd(m, a₁, ..., a_(d+1)) * m^d`。 -/
theorem periodicLinearCongruenceBox_card_closed_succ
    (d t m : ℕ) (a : Fin (d + 1) → ℤ)
    (b : ZMod m) (hm : 0 < m)
    (c : Fin (d + 1) → Fin m)
    (hc : (∑ i : Fin (d + 1),
      (a i : ZMod m) * ((c i).val : ZMod m)) = b) :
    Fintype.card (periodicLinearCongruenceBox (d + 1) t m a b) =
      t ^ (d + 1) *
        (multivariableLinearGCD
          (Finset.univ : Finset (Fin (d + 1))) a m * m ^ d) := by
  classical
  calc
    Fintype.card (periodicLinearCongruenceBox (d + 1) t m a b) =
        Fintype.card ((Fin (d + 1) → Fin t) ×
          fundamentalLinearCongruenceBox (d + 1) m a b) :=
      Fintype.card_congr (periodicLinearCongruenceBoxEquiv (d + 1) t m a b)
    _ = t ^ (d + 1) *
          Fintype.card (fundamentalLinearCongruenceBox (d + 1) m a b) := by
      simp [Fintype.card_prod]
    _ = _ := by
      rw [fundamentalLinearCongruenceBox_card_closed_succ d m a b hm c hc]

end ArithLemmas.Mathlib.Finset
