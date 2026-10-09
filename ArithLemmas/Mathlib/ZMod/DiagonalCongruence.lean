module

public import ArithLemmas.Mathlib.ZMod.MatrixCongruence
public import Mathlib.Data.Fintype.BigOperators

/-!
# 対角合同式の可解性と厳密なファイバー計数

Smith 標準形の対角係数は自然数の非負標準代表で取る。
`d_i x_i = b_i` (mod `m`) が可解である条件は `gcd(m,d_i) ∣ b_i.val`。
可解時の剰余解数は各座標について `gcd(m,d_i)` 個である。
法は正とし、係数 `d_i = 0` も含めて取り扱う。
-/

public section

namespace ArithLemmas.Mathlib.ZMod

open ArithLemmas.Mathlib.Int

/-- 1つの剰余乗法を表す加法準同型。 -/
def scalarModHom (m a : ℕ) : ZMod m →+ ZMod m where
  toFun x := (a : ZMod m) * x
  map_zero' := by simp
  map_add' := by intro x y; simp [mul_add]

/-- 1つの剰余乗法のファイバー。 -/
@[expose] def scalarModFiber (m a : ℕ) (b : ZMod m) :=
  {x : ZMod m // (a : ZMod m) * x = b}

/-- 既知解を引くと、1変数ファイバーは核と同値。 -/
noncomputable def scalarModFiberEquivKernel (m a : ℕ) (b c : ZMod m)
    (hc : (a : ZMod m) * c = b) :
    scalarModFiber m a b ≃ (scalarModHom m a).ker where
  toFun x := ⟨x.val - c, by
    apply (AddMonoidHom.sub_mem_ker_iff (scalarModHom m a)).2
    change (a : ZMod m) * x.val = (a : ZMod m) * c
    exact x.property.trans hc.symm⟩
  invFun y := ⟨y.val + c, by
    have hy : (scalarModHom m a) y.val = 0 :=
      (AddMonoidHom.mem_ker).mp y.property
    change (scalarModHom m a) (y.val + c) = b
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

/-- 剰余乗法の像は `a` が生成する巡回加法部分群。 -/
theorem scalarModHom_range_eq_zmultiples (m a : ℕ) (hm : 0 < m) :
    (scalarModHom m a).range = AddSubgroup.zmultiples (a : ZMod m) := by
  let : NeZero m := ⟨hm.ne'⟩
  have hgen : (a : ZMod m) ∈ (scalarModHom m a).range := by
    refine ⟨1, ?_⟩
    change (a : ZMod m) * 1 = a
    simp
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hy
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(x.val : ℤ), ?_⟩
    change (x.val : ℤ) • (a : ZMod m) = (a : ZMod m) * x
    rw [zsmul_eq_mul]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, mul_comm]
  · intro y hy
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    exact (scalarModHom m a).range.zsmul_mem hgen k

/-- 剰余乗法の像の位数は `m / gcd(m,a)`。 -/
theorem scalarModHom_range_card (m a : ℕ) (hm : 0 < m) :
    Nat.card (scalarModHom m a).range = m / Nat.gcd m a := by
  let : NeZero m := ⟨hm.ne'⟩
  rw [scalarModHom_range_eq_zmultiples m a hm]
  change Nat.card (AddSubgroup.zmultiples (a : ZMod m)) = m / Nat.gcd m a
  rw [Nat.card_zmultiples, ZMod.addOrderOf_coe a hm.ne']

/-- 可解な一変数剰余乗法の解数は正確に `gcd(m,a)`。 -/
theorem scalarModFiber_card_eq_gcd (m a : ℕ) (b c : ZMod m)
    (hm : 0 < m) (hc : (a : ZMod m) * c = b) :
    Nat.card (scalarModFiber m a b) = Nat.gcd m a := by
  let : NeZero m := ⟨hm.ne'⟩
  have hdiv : Nat.gcd m a ∣ m := Nat.gcd_dvd_left m a
  have hgpos : 0 < Nat.gcd m a := Nat.gcd_pos_of_pos_left _ hm
  have hqpos : 0 < m / Nat.gcd m a :=
    Nat.div_pos (Nat.le_of_dvd hm hdiv) hgpos
  have hcount : Nat.card (scalarModHom m a).ker *
      Nat.card (scalarModHom m a).range = m := by
    have h := AddSubgroup.card_mul_index (scalarModHom m a).ker
    rw [AddSubgroup.index_ker (scalarModHom m a)] at h
    simpa [Nat.card_zmod] using h
  rw [scalarModHom_range_card m a hm] at hcount
  have hker : Nat.card (scalarModHom m a).ker = Nat.gcd m a := by
    apply Nat.eq_of_mul_eq_mul_right hqpos
    calc
      Nat.card (scalarModHom m a).ker * (m / Nat.gcd m a) = m := hcount
      _ = Nat.gcd m a * (m / Nat.gcd m a) := by
        rw [mul_comm, Nat.div_mul_cancel hdiv]
  exact (Nat.card_congr (scalarModFiberEquivKernel m a b c hc)).trans hker

/-- 1つの対角合同式の可解性はGCD整除で判定できる。 -/
theorem scalarModFiber_nonempty_iff_gcd_dvd (m a : ℕ) (b : ZMod m)
    (hm : 0 < m) :
    Nonempty (scalarModFiber m a b) ↔
      ((Nat.gcd m a : ℕ) : ℤ) ∣ ((b.val : ℕ) : ℤ) := by
  let : NeZero m := ⟨hm.ne'⟩
  have hbase := linearCongruence_exists_iff_gcd_dvd
    (a : ℤ) ((b.val : ℕ) : ℤ) m
  rw [Int.gcd_natCast_natCast] at hbase
  constructor
  · rintro ⟨⟨x, hx⟩⟩
    apply hbase.mp
    refine ⟨((x.val : ℕ) : ℤ), ?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ m).mp
    simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] using hx
  · intro hb
    obtain ⟨x, hx⟩ := hbase.mpr hb
    refine ⟨⟨(x : ZMod m), ?_⟩⟩
    have heq := (ZMod.intCast_eq_intCast_iff _ _ m).mpr hx
    simpa only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] using heq

/-- 有限個の対角合同条件を満たすベクトル。 -/
@[expose] def diagonalModFiber (n m : ℕ) (a : Fin n → ℕ)
    (b : Fin n → ZMod m) :=
  {x : Fin n → ZMod m // ∀ i, (a i : ZMod m) * x i = b i}

/-- 対角系の各座標は独立なので、ファイバーは1変数ファイバーの直積。 -/
noncomputable def diagonalModFiberEquivPi (n m : ℕ) (a : Fin n → ℕ)
    (b : Fin n → ZMod m) :
    diagonalModFiber n m a b ≃
      (∀ i : Fin n, scalarModFiber m (a i) (b i)) := by
  change
    {x : Fin n → ZMod m //
      ∀ i : Fin n, (a i : ZMod m) * x i = b i} ≃
    (∀ i : Fin n,
      {x : ZMod m // (a i : ZMod m) * x = b i})
  exact Equiv.subtypePiEquivPi
    (α := Fin n)
    (β := fun _ => ZMod m)
    (p := fun i x => (a i : ZMod m) * x = b i)

/-- 対角合同系の可解性の必要十分条件。 -/
theorem diagonalModFiber_nonempty_iff_gcd_dvd (n m : ℕ)
    (a : Fin n → ℕ) (b : Fin n → ZMod m) (hm : 0 < m) :
    Nonempty (diagonalModFiber n m a b) ↔
      ∀ i : Fin n, ((Nat.gcd m (a i) : ℕ) : ℤ) ∣ ((b i).val : ℤ) := by
  constructor
  · rintro ⟨⟨x, hx⟩⟩ i
    exact (scalarModFiber_nonempty_iff_gcd_dvd m (a i) (b i) hm).mp
      ⟨⟨x i, hx i⟩⟩
  · intro h
    classical
    have hs (i : Fin n) : ∃ x : ZMod m, (a i : ZMod m) * x = b i := by
      obtain ⟨⟨x, hx⟩⟩ :=
        (scalarModFiber_nonempty_iff_gcd_dvd m (a i) (b i) hm).mpr (h i)
      exact ⟨x, hx⟩
    choose x hx using hs
    exact ⟨⟨x, hx⟩⟩

/-- 可解な対角合同系の解数は各座標のGCDの積に等しい。 -/
theorem diagonalModFiber_card_eq_prod_gcd (n m : ℕ)
    (a : Fin n → ℕ) (b : Fin n → ZMod m) (hm : 0 < m)
    (c : Fin n → ZMod m)
    (hc : ∀ i, (a i : ZMod m) * c i = b i) :
    Nat.card (diagonalModFiber n m a b) = ∏ i : Fin n, Nat.gcd m (a i) := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  calc
    Nat.card (diagonalModFiber n m a b) =
        Nat.card (∀ i : Fin n, scalarModFiber m (a i) (b i)) :=
          Nat.card_congr (diagonalModFiberEquivPi n m a b)
    _ = ∏ i : Fin n, Nat.card (scalarModFiber m (a i) (b i)) := by
      rw [Nat.card_pi]
    _ = ∏ i : Fin n, Nat.gcd m (a i) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact scalarModFiber_card_eq_gcd m (a i) (b i) (c i) hm (hc i)

end ArithLemmas.Mathlib.ZMod
