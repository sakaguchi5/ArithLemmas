module

public import ArithLemmas.Pure.Defs.Int.Basic

/-!
# 整数の導出定理

Lean 本体の整数型、合同条件、区間条件、基本証明戦術だけを使用する。
-/

public section

namespace ArithLemmas.Pure.Int

open ArithLemmas.Pure.Defs.Int

/-- どの整数も自分自身と合同である。-/
theorem modEq_refl (m a : Int) : modEq m a a := rfl

/-- 合同関係は対称である。-/
theorem modEq_symm {m a b : Int} (h : modEq m a b) : modEq m b a := h.symm

/-- 同じ法に関する合同関係は推移的である。-/
theorem modEq_trans {m a b c : Int}
    (hab : modEq m a b) (hbc : modEq m b c) : modEq m a c := hab.trans hbc

/-- 等しい二つの整数は、任意の法に関して合同である。-/
theorem modEq_of_eq (m : Int) {a b : Int} (h : a = b) : modEq m a b := by
  subst b
  rfl

/-- 順序を満たす区間の左端は、その区間に属する。-/
theorem interval_left {a b : Int} (hab : a ≤ b) : inInterval a b a :=
  ⟨Int.le_refl a, hab⟩

/-- 順序を満たす区間の右端は、その区間に属する。-/
theorem interval_right {a b : Int} (hab : a ≤ b) : inInterval a b b :=
  ⟨hab, Int.le_refl b⟩

/-- 区間に属することから、上端と下端の不等式が得られる。-/
theorem interval_bounds {a b x : Int} (hx : inInterval a b x) :
    a ≤ x ∧ x ≤ b := hx

/-- 区間と点を同じだけ平行移動しても、所属関係は変わらない。-/
theorem interval_translate (l u x t : Int) :
    inInterval l u x ↔ inInterval (l + t) (u + t) (x + t) := by
  simp only [inInterval]
  omega

/-- 二つの区間からそれぞれ選んだ整数の和は、端点を足した区間に入る。-/
theorem interval_add {l u x l' u' y : Int}
    (hx : inInterval l u x) (hy : inInterval l' u' y) :
    inInterval (l + l') (u + u') (x + y) := by
  rcases hx with ⟨hlx, hxu⟩
  rcases hy with ⟨hly, hyu⟩
  constructor <;> omega

/-- 区間の一部分に含まれる点は、拡げた区間にも含まれる。-/
theorem interval_mono {l u x l' u' : Int}
    (hx : inInterval l u x) (hleft : l' ≤ l) (hright : u ≤ u') :
    inInterval l' u' x := by
  rcases hx with ⟨hlx, hxu⟩
  exact ⟨Int.le_trans hleft hlx, Int.le_trans hxu hright⟩

end ArithLemmas.Pure.Int
