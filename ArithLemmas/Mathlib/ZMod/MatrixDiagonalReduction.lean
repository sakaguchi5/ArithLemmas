module

public import ArithLemmas.Mathlib.ZMod.DiagonalCongruence

/-!
# 整数行列の対角化証明書と連立合同式の可解性・解数

正の整数法で整数行列が、行・列の可逆な座標変換により
非負対角係数をもつ作用へ変換できた場合の普遍定理。

対角化の証明書を前提とする定理であり、任意の整数行列にその
証明書が存在するという Smith 標準形の存在定理そのものはここでは主張しない。
この区別により、数学的に未証明の仮定を暗黙に追加しない。
-/

public section

namespace ArithLemmas.Mathlib.ZMod

/-- 正方整数行列の剰余作用を非負対角作用に変換する証明書。
行の可逆変換 `rows`、列の可逆変換 `cols` を陽に保持する。 -/
structure MatrixDiagonalReduction (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) where
  diagonal : Fin n → ℕ
  rows : (Fin n → ZMod m) ≃+ (Fin n → ZMod m)
  cols : (Fin n → ZMod m) ≃+ (Fin n → ZMod m)
  factorization : ∀ x : Fin n → ZMod m,
    matrixModForm n n m A x =
      rows (fun i => (diagonal i : ZMod m) * (cols x) i)

/-- 対角化証明書は行列合同系と対角合同系のファイバーを同値にする。 -/
noncomputable def matrixDiagonalFiberEquiv (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (cert : MatrixDiagonalReduction n m A) (b : Fin n → ZMod m) :
    matrixModFiber n n m A b ≃
      diagonalModFiber n m cert.diagonal (cert.rows.symm b) where
  toFun x := ⟨cert.cols x.val, by
    have hh : cert.rows
        (fun i => (cert.diagonal i : ZMod m) * (cert.cols x.val) i) = b :=
      (cert.factorization x.val).symm.trans x.property
    have heq :
        (fun i => (cert.diagonal i : ZMod m) * (cert.cols x.val) i) =
          cert.rows.symm b := by
      apply cert.rows.injective
      simpa only [AddEquiv.apply_symm_apply] using hh
    exact congrFun heq⟩
  invFun y := ⟨cert.cols.symm y.val, by
    rw [cert.factorization]
    have heq :
        (fun i => (cert.diagonal i : ZMod m) * y.val i) =
          cert.rows.symm b := by
      funext i
      exact y.property i
    simpa only [AddEquiv.apply_symm_apply] using congrArg cert.rows heq⟩
  left_inv x := by
    apply Subtype.ext
    simp only [AddEquiv.symm_apply_apply]
  right_inv y := by
    apply Subtype.ext
    simp only [AddEquiv.apply_symm_apply]

/-- 対角化が与えられた行列合同式の可解性は座標ごとのGCD整除に等しい。 -/
theorem matrixDiagonal_nonempty_iff_gcd_dvd (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (cert : MatrixDiagonalReduction n m A)
    (b : Fin n → ZMod m) (hm : 0 < m) :
    Nonempty (matrixModFiber n n m A b) ↔
      ∀ i : Fin n,
        ((Nat.gcd m (cert.diagonal i) : ℕ) : ℤ) ∣
          (((cert.rows.symm b) i).val : ℤ) := by
  exact (Equiv.nonempty_congr
    (matrixDiagonalFiberEquiv n m A cert b)).trans
      (diagonalModFiber_nonempty_iff_gcd_dvd
        n m cert.diagonal (cert.rows.symm b) hm)

/-- 可解な行列合同系のファイバーの位数は対角係数のGCDの積。 -/
theorem matrixDiagonal_fiber_card_eq_prod_gcd (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (cert : MatrixDiagonalReduction n m A)
    (b : Fin n → ZMod m) (hm : 0 < m)
    (c : Fin n → ZMod m) (hc : matrixModForm n n m A c = b) :
    Nat.card (matrixModFiber n n m A b) =
      ∏ i : Fin n, Nat.gcd m (cert.diagonal i) := by
  have hdiag : ∀ i,
      (cert.diagonal i : ZMod m) * (cert.cols c) i =
        (cert.rows.symm b) i :=
    (matrixDiagonalFiberEquiv n m A cert b ⟨c, hc⟩).property
  calc
    Nat.card (matrixModFiber n n m A b) =
        Nat.card (diagonalModFiber n m cert.diagonal (cert.rows.symm b)) :=
          Nat.card_congr (matrixDiagonalFiberEquiv n m A cert b)
    _ = ∏ i : Fin n, Nat.gcd m (cert.diagonal i) :=
      diagonalModFiber_card_eq_prod_gcd n m
        cert.diagonal (cert.rows.symm b) hm (cert.cols c) hdiag

/-- 整数の連立合同式の可解性判定：証明書の対角GCD条件に還元する。 -/
theorem integerMatrix_diagonal_exists_iff (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ)
    (cert : MatrixDiagonalReduction n m A) (hm : 0 < m) :
    (∃ x : Fin n → ℤ,
        ∀ i, (integerMatrixForm n n A x) i ≡ b i [ZMOD (m : ℤ)]) ↔
      ∀ i : Fin n,
        ((Nat.gcd m (cert.diagonal i) : ℕ) : ℤ) ∣
          (((cert.rows.symm (fun j => (b j : ZMod m))) i).val : ℤ) := by
  exact (integerMatrix_exists_iff_modFiber n n m A b hm).trans
    (matrixDiagonal_nonempty_iff_gcd_dvd n m A cert
      (fun i => (b i : ZMod m)) hm)

/-- 可解な行列合同式の周期基本箱内の解数と像の位数の積。 -/
theorem matrixDiagonal_fiber_card_mul_range (n m : ℕ)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (cert : MatrixDiagonalReduction n m A)
    (b : Fin n → ZMod m) (hm : 0 < m)
    (c : Fin n → ZMod m) (hc : matrixModForm n n m A c = b) :
    (∏ i : Fin n, Nat.gcd m (cert.diagonal i)) *
      Nat.card (matrixModHom n n m A).range = m ^ n := by
  rw [← matrixDiagonal_fiber_card_eq_prod_gcd n m A cert b hm c hc]
  exact matrixModFiber_card_mul_range n n m A b hm c hc

end ArithLemmas.Mathlib.ZMod
