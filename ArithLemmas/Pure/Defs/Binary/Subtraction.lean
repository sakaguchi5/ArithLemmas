module

public import ArithLemmas.Pure.Defs.Binary.Representation

/-!
# 二進減算と借りの薄い定義（第2段階2B）

下位桁から並べた `List Bool` の減算を定義する。
借りは `Bool` で表し、定義には演算の正当性を埋め込まない。
原典：OpenAI `OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`
（`KS.W19.differenceDigit`、`nextBorrow`、`subtractBits`）。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Binary

/-- 一桁の減算における差のビット。第三引数は入ってくる借りである。 -/
def differenceDigit (a b borrow : Bool) : Bool :=
  Bool.xor (Bool.xor a b) borrow

/-- 一桁の減算によって次の桁へ伝播する借り。 -/
def nextBorrow (a b borrow : Bool) : Bool :=
  (!a && (b || borrow)) || (b && borrow)

/-- 下位桁から借りを伝播させる二進減算。
両方の入力が尽きたときは空列を返す。数値的正当性は導出層で証明する。 -/
def subtractBits : List Bool → List Bool → Bool → List Bool
  | [], [], _ => []
  | [], b :: bs, c =>
      differenceDigit false b c :: subtractBits [] bs (nextBorrow false b c)
  | a :: as, [], c =>
      differenceDigit a false c :: subtractBits as [] (nextBorrow a false c)
  | a :: as, b :: bs, c =>
      differenceDigit a b c :: subtractBits as bs (nextBorrow a b c)
termination_by xs ys _ => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

end ArithLemmas.Pure.Defs.Binary
