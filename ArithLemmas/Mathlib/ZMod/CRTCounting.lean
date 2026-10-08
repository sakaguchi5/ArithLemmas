module

public import ArithLemmas.Mathlib.ZMod.ResidueLifting
/-!
# CRTによる有限区間・有限次元の正確な計数（第4段階4E-2）

原典：`OAI/Geometry/HeilbronnTriangle/CRTLifting.lean`。
互いに素な法 `h`, `q` の二つの剰余条件を、一つの法 `h*q` に変換する。
同値写像を使い、長さ `t*(h*q)` の区間で解の個数が `t` であること、
`d` 座標では `t^d` であることを証明する。
-/

noncomputable section
@[expose] public section

namespace ArithLemmas.Mathlib.ZMod

/-- CRTを通じて二つのZMod剰余条件は積の法に対する一つの条件になる。 -/
theorem crt_residue_iff (h q : ℕ) (hc : h.Coprime q)
    (a : ZMod h) (b : ZMod q) (x : ℕ) :
    ((x : ZMod h) = a ∧ (x : ZMod q) = b) ↔
      (x : ZMod (h * q)) = (ZMod.chineseRemainder hc).symm (a, b) := by
  constructor
  · intro hx
    apply (ZMod.chineseRemainder hc).injective
    simpa only [map_natCast, RingEquiv.apply_symm_apply, Prod.ext_iff, Prod.fst_natCast,
      Prod.snd_natCast] using hx
  · intro hx
    have hh := congrArg (ZMod.chineseRemainder hc) hx
    simpa only [map_natCast, RingEquiv.apply_symm_apply, Prod.ext_iff, Prod.fst_natCast,
      Prod.snd_natCast] using hh

/-- 二つの剰余を同時に満たす `t` 周期分の代表元と `Fin t` の同値。 -/
def crtLiftEquiv (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : ZMod h) (b : ZMod q) :
    {x : Fin (t * (h * q)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} ≃ Fin t :=
  (Equiv.subtypeEquivRight fun (x : Fin (t * (h * q))) =>
      crt_residue_iff h q hc a b x.val).trans
    (zmodResidueLiftEquiv (h * q) t ((ZMod.chineseRemainder hc).symm (a, b)))

/-- 互いに素な二法について、長さ `t*h*q` の区間内には同時解が `t` 個ある。 -/
theorem card_crt_lifts (h q t : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : ZMod h) (b : ZMod q) :
    Fintype.card {x : Fin (t * (h * q)) //
      (x.val : ZMod h) = a ∧ (x.val : ZMod q) = b} = t := by
  rw [Fintype.card_congr (crtLiftEquiv h q t hc a b), Fintype.card_fin]

/-- 各座標で独立の剰余条件を満たすベクトルの同値。 -/
def crtVectorLiftEquiv (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    {x : Fin d → Fin (t * (h * q)) // ∀ i,
      ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} ≃
      (Fin d → Fin t) :=
  Equiv.subtypePiEquivPi.trans
    (Equiv.piCongrRight fun i => crtLiftEquiv h q t hc (a i) (b i))

/-- `d` 座標の合同制約を満たす代表ベクトルは `t^d` 個存在する。 -/
theorem card_crt_vector_lifts (h q t d : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (a : Fin d → ZMod h) (b : Fin d → ZMod q) :
    Fintype.card {x : Fin d → Fin (t * (h * q)) // ∀ i,
      ((x i).val : ZMod h) = a i ∧ ((x i).val : ZMod q) = b i} = t ^ d := by
  rw [Fintype.card_congr (crtVectorLiftEquiv h q t d hc a b)]
  simp

end ArithLemmas.Mathlib.ZMod
end
end
