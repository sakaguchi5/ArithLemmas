module

/-!
# 整数の正部分・負部分：薄い定義

Lean標準の Int の二つの構成子に基づいて、整数の分解に必要な
自然数値の部分だけを定義する。Mathlib に依存しない。
原典：Computability/RationalHitting/SignedArithmetic (`positivePart`, `negativePart`)。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Int

/-- 整数の非負部分。負の整数では0、非負整数では元の自然数値を返す。 -/
def positivePart : Int → Nat
  | .ofNat n => n
  | .negSucc _ => 0

/-- 整数の負部分の大きさ。非負整数では0、負整数では絶対値を返す。 -/
def negativePart : Int → Nat
  | .ofNat _ => 0
  | .negSucc n => n + 1

end ArithLemmas.Pure.Defs.Int
