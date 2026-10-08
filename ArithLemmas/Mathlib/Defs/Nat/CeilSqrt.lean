module

public import Mathlib.Data.Nat.Sqrt

/-!
# 自然数の切り上げ平方根：薄い定義（第4段階4A）

整数平方根 `Nat.sqrt` を用い、最小の平方根の上側近似を定義する。
ここには定義のみを置き、正当性・評価は `Mathlib/Nat/CeilSqrt.lean` に置く。
原典：OpenAI `OAI/Algebra/DepthFive/Basic.lean` (`Problem335.ceilSqrt`)。
-/

@[expose] public section

namespace ArithLemmas.Mathlib.Defs.Nat

/-- 自然数 `n` の平方根の切り上げ。完全平方数では整数平方根そのものになる。 -/
def ceilSqrt (n : ℕ) : ℕ :=
  Nat.sqrt n + if (Nat.sqrt n) ^ 2 = n then 0 else 1

end ArithLemmas.Mathlib.Defs.Nat
