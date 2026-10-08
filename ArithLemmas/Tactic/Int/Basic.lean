module

public import ArithLemmas.Pure.Int.Basic

/-!
# 整数の自動化された証明

区間の移動や加算に関する性質を、Lean 本体の `omega` で証明する。
このファイルは Mathlib を必要としない。
-/

public section

namespace ArithLemmas.Tactic.Int

open ArithLemmas.Pure.Defs.Int

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

end ArithLemmas.Tactic.Int
