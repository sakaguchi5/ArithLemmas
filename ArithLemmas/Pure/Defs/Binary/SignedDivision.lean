module

public import ArithLemmas.Pure.Defs.Binary.Division

/-!
# 符号付き二進除算の薄い定義（第2段階2D）

二進列の数値を正整数または負整数として解釈する。
負の場合は `Int.negSucc` を用い、ビット列の値 `n` を整数 `-(n+1)` に対応させる。
符号付き除算は、2C の自然数除算と 2B の減算から構成する。
原典：OpenAI `OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`
（`KS.W19.signedBitsValue`、`divideSignedBits`、`negativeOfInt`）。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Binary

/-- 符号と二進列から整数を復元する。`true` は `-(n+1)` を表す。 -/
def signedBitsValue (negative : Bool) (xs : List Bool) : Int :=
  if negative then Int.negSucc (bitsValue xs) else Int.ofNat (bitsValue xs)

/-- 整数の構成子から符号を得る。負の整数のときだけ `true` を返す。 -/
def negativeOfInt : Int → Bool
  | .ofNat _ => false
  | .negSucc _ => true

/-- 符号付き整数の二進表現へ渡す自然数ペイロード。`-(n+1)` には `n` を使う。 -/
def signedPayload : Int → Nat
  | .ofNat n => n
  | .negSucc n => n

/-- 符号付き二進長除算。正の除数に対する商と非負の余りを返す。
負の被除数では、商の `Int.negSucc` 表現に合わせて余りを `d-1-r` に補正する。 -/
def divideSignedBits (negative : Bool) (divisor xs : List Bool) : List Bool × List Bool :=
  let qr := divideBits divisor xs
  if negative then
    (qr.1, subtractBits (subtractBits divisor [true] false) qr.2 false)
  else qr

end ArithLemmas.Pure.Defs.Binary
