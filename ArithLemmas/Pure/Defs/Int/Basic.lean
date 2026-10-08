/-!
# 整数の薄い定義

Lean 本体の整数型 `Int` を使い、区間と合同関係を標準的な演算から作る。
新しい構造体や公理は導入しない。
-/

namespace ArithLemmas.Pure.Defs.Int

/-- 整数が両端を含む区間に属するという条件。-/
def inInterval (lower upper x : Int) : Prop := lower ≤ x ∧ x ≤ upper

/-- 同じ法に関して、二つの整数の剰余が等しいという条件。-/
def modEq (modulus a b : Int) : Prop := a % modulus = b % modulus

end ArithLemmas.Pure.Defs.Int
