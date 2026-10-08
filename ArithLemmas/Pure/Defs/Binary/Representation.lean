module

/-!
# 二進表現の薄い定義

ビット列を下位桁から並べた `List Bool` として解釈する。
`bitsValue` は OpenAI 数学証明群の `KS.W19.bitsValue` と同じ意味を持つ。
ここでは値の定義だけを行い、桁数上界や基本性質は導出層に置く。
原典：`OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Binary

/-- 真を１、偽を０とみなす二進数字の値。 -/
def digit (b : Bool) : Nat := if b then 1 else 0

/-- 下位桁を先頭に置く二進列の表す自然数。 -/
def bitsValue : List Bool → Nat
  | [] => 0
  | b :: bs => digit b + 2 * bitsValue bs

end ArithLemmas.Pure.Defs.Binary
