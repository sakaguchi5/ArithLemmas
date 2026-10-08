module

public import ArithLemmas.Mathlib.ZMod.CRTCounting
public import Mathlib.Data.Int.Interval
/-!
# 整数区間のCRTによる正確な計数（第4段階4E-2）

原典：`OAI/Geometry/HeilbronnTriangle/CRTLifting.lean`。
自然数の代表元計数を開始点が任意の整数である区間に移し、
座標ごとに異なる区間開始点を持つ有限次元の正確な個数を導出する。
-/

noncomputable section
@[expose] public section

namespace ArithLemmas.Mathlib.Int

open ArithLemmas.Mathlib.ZMod

/-- 自然数の有限区間を任意の整数始点の区間に平行移動する同値。 -/
def intIntervalEquiv (N : ℕ) (s : ℤ) : Fin N ≃ Set.Ico s (s + N) where
  toFun x := ⟨s + x.val, by
    constructor
    · omega
    · have hx := x.is_lt
      omega⟩
  invFun x := ⟨(x.val - s).toNat, by
    rcases x.property with ⟨hx0, hx1⟩
    omega⟩
  left_inv x := by
    apply Fin.ext
    simp
  right_inv x := by
    apply Subtype.ext
    rcases x.property with ⟨hx0, hx1⟩
    dsimp
    omega

/-- 任意の整数始点を持つCRT同時剰余の持ち上げと `Fin t` の同値。 -/
def intCRTLiftEquiv (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : ℤ) (a : ZMod h) (b : ZMod q) :
    {x : Set.Ico s (s + (t * (h * q) : ℕ)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} ≃ Fin t := by
  let e := (intIntervalEquiv (t * (h * q)) s).subtypeEquiv
    (p := fun x => (x.val : ZMod h) = a - (s : ZMod h) ∧
      (x.val : ZMod q) = b - (s : ZMod q))
    (q := fun x => (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b)
    (by
      intro x
      change ((x.val : ZMod h) = a - (s : ZMod h) ∧
        (x.val : ZMod q) = b - (s : ZMod q)) ↔
        (((s + x.val : ℤ) : ZMod h) = a ∧ ((s + x.val : ℤ) : ZMod q) = b)
      simp only [eq_sub_iff_add_eq, Int.cast_add, Int.cast_natCast]
      simp only [add_comm])
  exact e.symm.trans (crtLiftEquiv h q t hc (a - (s : ZMod h)) (b - (s : ZMod q)))

/-- 整数半開区間の長さが `t*h*q` なら、指定した二剰余の同時解は `t` 個。 -/
theorem card_int_crt_lifts (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : ℤ) (a : ZMod h) (b : ZMod q) :
    Fintype.card {x : Set.Ico s (s + (t * (h * q) : ℕ)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} = t := by
  rw [Fintype.card_congr (intCRTLiftEquiv h q t hc s a b), Fintype.card_fin]

/-- 座標ごとに始点の異なるCRT制約付き整数ベクトルの同値。 -/
def intCRTVectorLiftEquiv (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    {x : (i : Fin d) → Set.Ico (s i) (s i + (t * (h * q) : ℕ)) // ∀ i,
      ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} ≃
      (Fin d → Fin t) :=
  Equiv.subtypePiEquivPi.trans
    (Equiv.piCongrRight fun i => intCRTLiftEquiv h q t hc (s i) (a i) (b i))

/-- `d` 個の任意の整数区間でのCRT条件を満たすベクトルは `t^d` 個。 -/
theorem card_int_crt_vector_lifts (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Fintype.card
      {x : (i : Fin d) → Set.Ico (s i) (s i + (t * (h * q) : ℕ)) // ∀ i,
        ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} = t ^ d := by
  rw [Fintype.card_congr (intCRTVectorLiftEquiv h q t d hc s a b)]
  simp

/-- 区間長 `N` が `h*q` の倍数なら、各座標に `N/(h*q)` 個の選択肢がある。 -/
theorem card_int_crt_vector_lifts_of_dvd (h q N d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hN : h * q ∣ N) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Fintype.card
      {x : (i : Fin d) → Set.Ico (s i) (s i + N) // ∀ i,
        ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} =
      (N / (h * q)) ^ d := by
  have heq : N / (h * q) * (h * q) = N := Nat.div_mul_cancel hN
  have H := card_int_crt_vector_lifts h q (N / (h * q)) d hc s a b
  rw [heq] at H
  exact H

/-- 周期数が正なら、合同条件を満たす整数ベクトルが存在する。 -/
theorem int_crt_vector_lifts_nonempty (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (ht : 0 < t) (s : Fin d → ℤ)
    (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Nonempty
      {x : (i : Fin d) → Set.Ico (s i) (s i + (t * (h * q) : ℕ)) // ∀ i,
        ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} :=
  ⟨(intCRTVectorLiftEquiv h q t d hc s a b).symm (fun _ => ⟨0, ht⟩)⟩

end ArithLemmas.Mathlib.Int
end
end
