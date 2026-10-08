module

public import ArithLemmas.Mathlib.ZMod.CRTBridge
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# 単一剰余の有限区間への持ち上げ（第4段階4E-2）

原典：`OAI/Geometry/HeilbronnTriangle/CRTLifting.lean`。
法 `m` の一つの剰余類は、長さ `t * m` の区間にちょうど `t` 個の代表元を持つ。
`ZMod` の値と、有限区間の自然数代表元を明示的な同値写像で対応させる。
-/

noncomputable section
@[expose] public section

namespace ArithLemmas.Mathlib.ZMod

/-- 法 `m` の指定剰余を持つ長さ `t*m` の有限区間は `Fin t` と同値。 -/
def zmodResidueLiftEquiv (m t : ℕ) [NeZero m] (r : ZMod m) :
    {x : Fin (t * m) // (x.val : ZMod m) = r} ≃ Fin t where
  toFun x := x.val.divNat
  invFun y := ⟨finProdFinEquiv (y, ⟨r.val, r.val_lt⟩), by
    change ((r.val + m * y.val : ℕ) : ZMod m) = r
    simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Fin.ext
    change r.val + m * (x.val.val / m) = x.val.val
    have hr : x.val.val % m = r.val := by
      simpa using congrArg ZMod.val x.property
    rw [← hr]
    exact Nat.mod_add_div _ _
  right_inv y := by
    apply Fin.ext
    change (r.val + m * y.val) / m = y.val
    rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (NeZero.ne m)),
      Nat.div_eq_of_lt r.val_lt, Nat.zero_add]

/-- 単一剰余を指定した `t` 周期分の代表元はちょうど `t` 個。 -/
theorem card_residue_lifts (m t : ℕ) [NeZero m] (r : ZMod m) :
    Fintype.card {x : Fin (t * m) // (x.val : ZMod m) = r} = t := by
  rw [Fintype.card_congr (zmodResidueLiftEquiv m t r), Fintype.card_fin]

end ArithLemmas.Mathlib.ZMod
end
end
