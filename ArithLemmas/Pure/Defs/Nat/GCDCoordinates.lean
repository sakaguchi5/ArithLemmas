module

/-!
# 自然数対の GCD 座標

自然数対の GCD と二つの縮約商だけを定義する。
問題固有の別名は設けず、標準形・復元・単射性は `Pure/Nat/GCD.lean`
で定理として導出する。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Nat

/-- 自然数対を、共通因子と二つの縮約座標に写す。 -/
def gcdCoordinates (v : Nat × Nat) : Nat × Nat × Nat :=
  (Nat.gcd v.1 v.2, v.1 / Nat.gcd v.1 v.2, v.2 / Nat.gcd v.1 v.2)

end ArithLemmas.Pure.Defs.Nat
