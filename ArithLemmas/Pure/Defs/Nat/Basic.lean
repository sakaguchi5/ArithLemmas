module

/-!
# 自然数の薄い定義

Lean 本体の `Nat`・`Nat.gcd`・自然数除算を使用する。
問題ごとの計算回路を持ち込まず、数そのものに対する操作だけを定義する。
ここでは数学的性質を定義に埋め込まず、別のファイルで定理として導く。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Nat

/-- 自然数の組に対する、指定回数だけのユークリッド互除法。
第２成分が０なら以後の状態を固定する。-/

def euclidRun : Nat → Nat → Nat → Nat × Nat
  | 0, a, b => (a, b)
  | k + 1, a, b => if b = 0 then (a, 0) else euclidRun k b (a % b)

/-- 整数の最大公約数と、最大公約数で割った商を組にする。-/
def gcdSplit (a d : Nat) : Nat × Nat := (Nat.gcd a d, a / Nat.gcd a d)

/-- 自然数の切り上げ除算を、通常の除算だけで定義する。
除数が０の場合も自然数の除算の規約に従う。-/
def ceilDiv (n t : Nat) : Nat := (n + t - 1) / t

end ArithLemmas.Pure.Defs.Nat
