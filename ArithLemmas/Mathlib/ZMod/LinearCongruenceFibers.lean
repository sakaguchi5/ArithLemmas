module

public import ArithLemmas.Mathlib.Int.MultivariableLinearCongruence
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Data.Fintype.BigOperators

/-!
# 多変数一次合同式の解空間（剰余環）

線形形式を加法群準同型として実装する。非空なファイバーはその核と
同値であるため、解集合は核の平行移動であり、すべての非空ファイバーは
同じ濃度を持つ。核と像の濃度の積による正確な計数公式も得られる。
-/

public section

namespace ArithLemmas.Mathlib.ZMod

open ArithLemmas.Mathlib.Int

/-- 剰余環上の多変数線形形式。 -/
@[expose] def modLinearForm (d m : ℕ) (a : Fin d → ℤ)
    (x : Fin d → ZMod m) : ZMod m :=
  ∑ i : Fin d, (a i : ZMod m) * x i

/-- 線形形式を有限加法群の準同型として表す。 -/
def modLinearHom (d m : ℕ) (a : Fin d → ℤ) :
    (Fin d → ZMod m) →+ ZMod m where
  toFun := modLinearForm d m a
  map_zero' := by
    simp [modLinearForm]
  map_add' := by
    intro x y
    simp [modLinearForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- 指定した剰余 `b` に写る解ベクトルの型。 -/
@[expose] def modLinearFiber (d m : ℕ) (a : Fin d → ℤ) (b : ZMod m) :=
  {x : Fin d → ZMod m // modLinearForm d m a x = b}

/-- 既知の解による平行移動は、非同次解集合と準同型の核を同一視する。 -/
noncomputable def modLinearFiberEquivKernel (d m : ℕ) (a : Fin d → ℤ)
    (b : ZMod m) (c : Fin d → ZMod m)
    (hc : modLinearForm d m a c = b) :
    modLinearFiber d m a b ≃ (modLinearHom d m a).ker where
  toFun x := ⟨x.val - c, by
    apply (AddMonoidHom.sub_mem_ker_iff (modLinearHom d m a)).2
    change modLinearForm d m a x.val = modLinearForm d m a c
    calc
      modLinearForm d m a x.val = b := x.property
      _ = modLinearForm d m a c := hc.symm⟩
  invFun y := ⟨y.val + c, by
    have hy : (modLinearHom d m a) y.val = 0 :=
      (AddMonoidHom.mem_ker).mp y.property
    change (modLinearHom d m a) (y.val + c) = b
    rw [map_add, hy, zero_add]
    exact hc⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    exact sub_add_cancel x.val c
  right_inv y := by
    apply Subtype.ext
    dsimp
    exact add_sub_cancel_right y.val c

/-- 多変数合同式の剰余解が存在することと、整数係数の GCD 整除性は同値。 -/
theorem modLinearFiber_nonempty_iff_gcd_dvd
    (d m : ℕ) (a : Fin d → ℤ) (b : ℤ) (hm : 0 < m) :
    Nonempty (modLinearFiber d m a (b : ZMod m)) ↔
      (multivariableLinearGCD (Finset.univ : Finset (Fin d)) a m : ℤ) ∣ b := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  have hcast (x : Fin d → ℤ) :
      ((multivariableLinearForm Finset.univ a x : ℤ) : ZMod m) =
        modLinearForm d m a (fun i => (x i : ZMod m)) := by
    simp only [multivariableLinearForm, modLinearForm, Int.cast_sum, Int.cast_mul]
  constructor
  · rintro ⟨⟨y, hy⟩⟩
    apply (multivariableLinearCongruence_exists_iff_gcd_dvd
      (Finset.univ : Finset (Fin d)) a b m).mp
    refine ⟨fun i => (y i).val, ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ m).mp
    calc
      ((multivariableLinearForm Finset.univ a (fun i => ((y i).val : ℤ)) : ℤ) : ZMod m) =
          modLinearForm d m a (fun i => (((y i).val : ℤ) : ZMod m)) :=
        hcast _
      _ = modLinearForm d m a y := by
        congr 1
        funext i
        simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (y i)
      _ = (b : ZMod m) := hy
  · intro hb
    obtain ⟨x, hx⟩ :=
      (multivariableLinearCongruence_exists_iff_gcd_dvd
        (Finset.univ : Finset (Fin d)) a b m).mpr hb
    refine ⟨⟨(fun i => (x i : ZMod m)), ?_⟩⟩
    exact (hcast x).symm.trans ((ZMod.intCast_eq_intCast_iff _ _ m).mpr hx)

/-- 一つの解があれば、ファイバーの正確な個数は核の位数に等しい。 -/
theorem modLinearFiber_card_eq_kernel_card
    (d m : ℕ) (a : Fin d → ℤ) (b : ZMod m)
    (hm : 0 < m) (c : Fin d → ZMod m)
    (hc : modLinearForm d m a c = b) :
    Nat.card (modLinearFiber d m a b) =
      Nat.card (modLinearHom d m a).ker := by
  let : NeZero m := ⟨hm.ne'⟩
  exact Nat.card_congr
    (modLinearFiberEquivKernel d m a b c hc)

/-- 核と像による正確な積公式：全剰余ベクトルは像と各ファイバーに分割される。 -/
theorem modLinearHom_kernel_mul_range_card
    (d m : ℕ) (a : Fin d → ℤ) (hm : 0 < m) :
    Nat.card (modLinearHom d m a).ker *
      Nat.card (modLinearHom d m a).range = m ^ d := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  let f := modLinearHom d m a
  have hcard :
      Nat.card f.ker * Nat.card f.range =
        Nat.card (Fin d → ZMod m) := by
    rw [← AddSubgroup.index_ker f]
    exact AddSubgroup.card_mul_index f.ker
  calc
    Nat.card (modLinearHom d m a).ker *
        Nat.card (modLinearHom d m a).range =
          Nat.card (Fin d → ZMod m) := hcard
    _ = m ^ d := by
      simp [Nat.card_eq_fintype_card,  ZMod.card]

/-- 可解な合同式の解数と像の位数との積は正確に `m^d`。 -/
theorem modLinearFiber_card_mul_range
    (d m : ℕ) (a : Fin d → ℤ) (b : ZMod m)
    (hm : 0 < m) (c : Fin d → ZMod m)
    (hc : modLinearForm d m a c = b) :
    Nat.card (modLinearFiber d m a b) *
      Nat.card (modLinearHom d m a).range = m ^ d := by
  rw [modLinearFiber_card_eq_kernel_card d m a b hm c hc]
  exact modLinearHom_kernel_mul_range_card d m a hm

/-- 線形形式の像は、係数と法の GCD が生成する巡回部分群に等しい。 -/
theorem modLinearHom_range_eq_zmultiples
    (d m : ℕ) (a : Fin d → ℤ) (hm : 0 < m) :
    (modLinearHom d m a).range =
      AddSubgroup.zmultiples
        ((multivariableLinearGCD (Finset.univ : Finset (Fin d)) a m : ℕ) : ZMod m) := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  let s : Finset (Fin d) := Finset.univ
  let g : ℕ := multivariableLinearGCD s a m
  have hdivcoeff (i : Fin d) : (g : ℤ) ∣ a i :=
    (Int.gcd_dvd_right (m : ℤ) (s.gcd a)).trans
      (Finset.gcd_dvd (Finset.mem_univ i))
  have hcastInt (x : Fin d → ℤ) :
      ((multivariableLinearForm s a x : ℤ) : ZMod m) =
        modLinearForm d m a (fun i => (x i : ZMod m)) := by
    simp only [s, multivariableLinearForm, modLinearForm,
      Int.cast_sum, Int.cast_mul]
  have hcastVal (x : Fin d → ZMod m) :
      ((multivariableLinearForm s a (fun i => ((x i).val : ℤ)) : ℤ) : ZMod m) =
        modLinearForm d m a x := by
    calc
      _ = modLinearForm d m a (fun i => (((x i).val : ℤ) : ZMod m)) := hcastInt _
      _ = modLinearForm d m a x := by
        congr 1
        funext i
        simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (x i)
  have hgenerator : (g : ZMod m) ∈ (modLinearHom d m a).range := by
    obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul s a
    let B : ℤ := Int.gcdB (m : ℤ) (s.gcd a)
    let v : Fin d → ℤ := fun i => f i * B
    have hsum : multivariableLinearForm s a v = (s.gcd a) * B := by
      calc
        multivariableLinearForm s a v =
            (∑ i ∈ s, a i * f i) * B := by
              unfold multivariableLinearForm v
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (s.gcd a) * B := by rw [← hf]
    have hbez : (g : ℤ) =
        (m : ℤ) * Int.gcdA (m : ℤ) (s.gcd a) + (s.gcd a) * B :=
      Int.gcd_eq_gcd_ab (m : ℤ) (s.gcd a)
    refine ⟨fun i => (v i : ZMod m), ?_⟩
    change modLinearForm d m a (fun i => (v i : ZMod m)) = (g : ZMod m)
    rw [← hcastInt v, hsum]
    have hh := congrArg (fun z : ℤ => (z : ZMod m)) hbez
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, zero_add] using hh.symm
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    have hdiv : (g : ℤ) ∣
        multivariableLinearForm s a (fun i => ((x i).val : ℤ)) := by
      apply Finset.dvd_sum
      intro i hi
      exact (hdivcoeff i).mul_right ((x i).val : ℤ)
    obtain ⟨k, hk⟩ := hdiv
    change modLinearForm d m a x ∈ AddSubgroup.zmultiples (g : ZMod m)
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨k, ?_⟩
    calc
      k • (g : ZMod m) = (((g : ℤ) * k : ℤ) : ZMod m) := by
        rw [zsmul_eq_mul]
        push_cast
        ring
      _ = ((multivariableLinearForm s a
          (fun i => ((x i).val : ℤ)) : ℤ) : ZMod m) := by rw [hk]
      _ = modLinearForm d m a x := hcastVal x
  · intro y hy
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact (modLinearHom d m a).range.zsmul_mem hgenerator k

/-- 像の大きさは `m / gcd(m, a₁, ..., a_d)` に正確に等しい。 -/
theorem modLinearHom_range_card
    (d m : ℕ) (a : Fin d → ℤ) (hm : 0 < m) :
    Nat.card (modLinearHom d m a).range =
      m / multivariableLinearGCD (Finset.univ : Finset (Fin d)) a m := by
  let g : ℕ := multivariableLinearGCD (Finset.univ : Finset (Fin d)) a m
  have hdiv : g ∣ m := by
    exact_mod_cast (Int.gcd_dvd_left (m : ℤ)
      ((Finset.univ : Finset (Fin d)).gcd a))
  rw [modLinearHom_range_eq_zmultiples d m a hm]
  change Nat.card (AddSubgroup.zmultiples (g : ZMod m)) = m / g
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe g hm.ne', Nat.gcd_eq_right hdiv]

/-- 正の法を持ち少なくとも一変数がある場合の完全な閉形式計数。 -/
theorem modLinearFiber_card_closed_succ
    (d m : ℕ) (a : Fin (d + 1) → ℤ) (b : ZMod m)
    (hm : 0 < m) (c : Fin (d + 1) → ZMod m)
    (hc : modLinearForm (d + 1) m a c = b) :
    Nat.card (modLinearFiber (d + 1) m a b) =
      multivariableLinearGCD (Finset.univ : Finset (Fin (d + 1))) a m * m ^ d := by
  let g : ℕ := multivariableLinearGCD
    (Finset.univ : Finset (Fin (d + 1))) a m
  have hdvd : g ∣ m := by
    exact_mod_cast (Int.gcd_dvd_left (m : ℤ)
      ((Finset.univ : Finset (Fin (d + 1))).gcd a))
  have hgpos : 0 < g := by
    by_contra hn
    have hzero : g = 0 := Nat.eq_zero_of_not_pos hn
    have hmzero : m = 0 := by simpa [hzero] using hdvd
    exact hm.ne' hmzero
  have hqpos : 0 < m / g := Nat.div_pos (Nat.le_of_dvd hm hdvd) hgpos
  have hcount := modLinearFiber_card_mul_range (d + 1) m a b hm c hc
  rw [modLinearHom_range_card (d + 1) m a hm] at hcount
  apply Nat.eq_of_mul_eq_mul_right hqpos
  calc
    Nat.card (modLinearFiber (d + 1) m a b) * (m / g) =
        m ^ (d + 1) := hcount
    _ = (g * m ^ d) * (m / g) := by
      rw [pow_succ]
      calc
        m ^ d * m = m ^ d * ((m / g) * g) := by rw [Nat.div_mul_cancel hdvd]
        _ = (g * m ^ d) * (m / g) := by ring

end ArithLemmas.Mathlib.ZMod
