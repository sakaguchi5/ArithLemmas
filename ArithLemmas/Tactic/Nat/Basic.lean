module

public import ArithLemmas.Pure.All

/-!
# 自然数の自動化された証明

定理の主張は自然数の基本演算のみで記述する。
不等式の証明には Lean 本体の `omega` を利用する。
このファイルは Mathlib を読み込まず、`Nat` の標準的な性質だけを使用する。
-/

public section

namespace ArithLemmas.Tactic.Nat

open ArithLemmas.Pure.Defs.Nat

/-- ０より大きく、かつ被除数より小さい数で割った余りは、
２倍しても元の被除数より小さい。
原典：量子因数分解における互除法の収束評価。-/
theorem euclid_two_halving {b r : Nat}
    (hr : 0 < r) (hrb : r < b) :
    2 * (b % r) < b := by
  by_cases h : 2 * r ≤ b
  · have hm := Nat.mod_lt b hr
    omega
  · have hb : b < 2 * r := by omega
    have hmod : b % r = b - r := by
      apply (Nat.mod_eq_sub_mod (Nat.le_of_lt hrb)).trans
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

/-- 正の除数で割った余りは、その除数より小さい。-/
theorem remainder_lt (a b : Nat) (hb : 0 < b) : a % b < b :=
  Nat.mod_lt a hb

/-- 切り上げ除算の結果と除数の積は、分子に除数を加えて１を引いた数以下。-/
theorem ceilDiv_mul_le (n t : Nat) : ceilDiv n t * t ≤ n + t - 1 := by
  change ((n + t - 1) / t) * t ≤ n + t - 1
  exact Nat.div_mul_le_self (n + t - 1) t

end ArithLemmas.Tactic.Nat
