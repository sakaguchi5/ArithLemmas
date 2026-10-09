module

public import ArithLemmas.Mathlib.ZMod.LinearCongruenceFibers
public import Mathlib.Data.Matrix.Mul

/-!
# 整数行列が定める剰余線形写像と解ファイバー

任意の長方形整数行列 `A : Matrix (Fin r) (Fin c) ℤ` を法 `m` で還元し、
`(ZMod m)^c → (ZMod m)^r` という加法準同型とみなす。
可解な系 `Ax = b` の解空間は核の平行移動である。
同時に、整数合同式と剰余環上の行列等式を対応させる。
-/

public section

namespace ArithLemmas.Mathlib.ZMod

/-- 整数行列による剰余ベクトル上の線形形式。 -/
@[expose] def matrixModForm (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (x : Fin c → ZMod m) : Fin r → ZMod m :=
  fun i => ∑ j : Fin c, (A i j : ZMod m) * x j

/-- 行列による剰余線形形式は、Mathlib の `Matrix.mulVec` と同じ作用。 -/
theorem matrixModForm_eq_mulVec (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (x : Fin c → ZMod m) :
    matrixModForm r c m A x =
      Matrix.mulVec (fun i j => (A i j : ZMod m)) x := by
  rfl

/-- 整数行列を法 `m` の剰余環上の加法準同型にする。 -/
def matrixModHom (r c m : ℕ) (A : Matrix (Fin r) (Fin c) ℤ) :
    (Fin c → ZMod m) →+ (Fin r → ZMod m) where
  toFun := matrixModForm r c m A
  map_zero' := by
    funext i
    simp [matrixModForm]
  map_add' x y := by
    funext i
    simp [matrixModForm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- 行列合同式の解の型。 -/
@[expose] def matrixModFiber (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m) :=
  {x : Fin c → ZMod m // matrixModForm r c m A x = b}

/-- 既知の解を原点に移動し、行列合同式のファイバーを核と同一視する。 -/
noncomputable def matrixModFiberEquivKernel (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m)
    (v : Fin c → ZMod m) (hv : matrixModForm r c m A v = b) :
    matrixModFiber r c m A b ≃ (matrixModHom r c m A).ker where
  toFun x := ⟨x.val - v, by
    apply (AddMonoidHom.sub_mem_ker_iff (matrixModHom r c m A)).2
    change matrixModForm r c m A x.val = matrixModForm r c m A v
    exact x.property.trans hv.symm⟩
  invFun y := ⟨y.val + v, by
    have hy : (matrixModHom r c m A) y.val = 0 :=
      (AddMonoidHom.mem_ker).mp y.property
    change (matrixModHom r c m A) (y.val + v) = b
    rw [map_add, hy, zero_add]
    exact hv⟩
  left_inv x := by
    apply Subtype.ext
    dsimp
    exact sub_add_cancel x.val v
  right_inv y := by
    apply Subtype.ext
    dsimp
    exact add_sub_cancel_right y.val v

/-- 行列合同式は、剰余環への写像の像に右辺が属するとき可解。 -/
theorem matrixModFiber_nonempty_iff_range (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m) :
    Nonempty (matrixModFiber r c m A b) ↔
      b ∈ (matrixModHom r c m A).range := by
  constructor
  · rintro ⟨⟨x, hx⟩⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩

/-- 非空ファイバーの濃度は核の濃度に一致する。 -/
theorem matrixModFiber_card_eq_kernel (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m)
    (v : Fin c → ZMod m) (hv : matrixModForm r c m A v = b) :
    Nat.card (matrixModFiber r c m A b) =
      Nat.card (matrixModHom r c m A).ker :=
  Nat.card_congr (matrixModFiberEquivKernel r c m A b v hv)

/-- 核と像の位数の積は、法 `m > 0` の場合、変数の全剰余ベクトルの数 `m^c`。 -/
theorem matrixModHom_kernel_mul_range_card (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (hm : 0 < m) :
    Nat.card (matrixModHom r c m A).ker *
      Nat.card (matrixModHom r c m A).range = m ^ c := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  let f := matrixModHom r c m A
  calc
    Nat.card f.ker * Nat.card f.range =
        Nat.card (Fin c → ZMod m) := by
          rw [← AddSubgroup.index_ker f]
          exact AddSubgroup.card_mul_index f.ker
    _ = m ^ c := by
      simp [Nat.card_eq_fintype_card, ZMod.card]

/-- 非空ファイバーの個数と像の大きさの積は `m^c`。 -/
theorem matrixModFiber_card_mul_range (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ZMod m)
    (hm : 0 < m) (v : Fin c → ZMod m)
    (hv : matrixModForm r c m A v = b) :
    Nat.card (matrixModFiber r c m A b) *
      Nat.card (matrixModHom r c m A).range = m ^ c := by
  rw [matrixModFiber_card_eq_kernel r c m A b v hv]
  exact matrixModHom_kernel_mul_range_card r c m A hm

/-- 整数行列の各行が与える整数線形形式。 -/
@[expose] def integerMatrixForm (r c : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (x : Fin c → ℤ) : Fin r → ℤ :=
  fun i => ∑ j : Fin c, A i j * x j

/-- 整数の行ごとの合同条件は、剰余環上の一つの行列等式と同値。 -/
theorem integerMatrix_modEq_iff (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ℤ) (x : Fin c → ℤ) :
    (∀ i, (integerMatrixForm r c A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      matrixModForm r c m A (fun j => (x j : ZMod m)) =
        (fun i => (b i : ZMod m)) := by
  constructor
  · intro h
    funext i
    have hi := (ZMod.intCast_eq_intCast_iff
      ((integerMatrixForm r c A x) i) (b i) m).mpr (h i)
    simpa only [integerMatrixForm, matrixModForm,
      Int.cast_sum, Int.cast_mul] using hi
  · intro h i
    apply (ZMod.intCast_eq_intCast_iff
      ((integerMatrixForm r c A x) i) (b i) m).mp
    have hi := congrFun h i
    simpa only [integerMatrixForm, matrixModForm,
      Int.cast_sum, Int.cast_mul] using hi

/-- 正の法における整数ベクトルでの可解性と剰余環での可解性は同値。 -/
theorem integerMatrix_exists_iff_modFiber (r c m : ℕ)
    (A : Matrix (Fin r) (Fin c) ℤ) (b : Fin r → ℤ) (hm : 0 < m) :
    (∃ x : Fin c → ℤ,
      ∀ i, (integerMatrixForm r c A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      Nonempty (matrixModFiber r c m A (fun i => (b i : ZMod m))) := by
  classical
  let : NeZero m := ⟨hm.ne'⟩
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨⟨(fun i => (x i : ZMod m)),
      (integerMatrix_modEq_iff r c m A b x).mp hx⟩⟩
  · rintro ⟨⟨y, hy⟩⟩
    let x : Fin c → ℤ := fun i => ((y i).val : ℤ)
    refine ⟨x, (integerMatrix_modEq_iff r c m A b x).mpr ?_⟩
    change matrixModForm r c m A
      (fun i => (((y i).val : ℤ) : ZMod m)) = _
    have hh : (fun i => (((y i).val : ℤ) : ZMod m)) = y := by
      funext i
      simpa only [Int.cast_natCast] using ZMod.natCast_zmod_val (y i)
    rw [hh]
    exact hy

end ArithLemmas.Mathlib.ZMod
