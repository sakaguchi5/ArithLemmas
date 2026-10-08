module

public import ArithLemmas.Pure.Defs.Binary.Comparison
public import ArithLemmas.Pure.Defs.Binary.Subtraction

/-!
# 自然数の二進除算の薄い定義（第2段階2C）

下位桁から並ぶ `List Bool` の被除数を上位桁から処理し、
商と余りのビット列を返す。ここでは数学的正当性を定義に埋め込まない。
正の除数についての正当性は `Pure/Binary/Division.lean` で証明する。
原典：OpenAI `OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`
（`KS.W19.divideBits`）。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Binary

/-- 二進長除算。第一引数が除数で、返り値は（商、余り）の組。
除数が０のときの数学的な正当性は主張しない。 -/
def divideBits (divisor : List Bool) : List Bool → List Bool × List Bool
  | [] => ([], [])
  | b :: bs =>
      let qr := divideBits divisor bs
      let trial := b :: qr.2
      if compareBits trial divisor = .lt then
        (false :: qr.1, trial)
      else
        (true :: qr.1, subtractBits trial divisor false)

end ArithLemmas.Pure.Defs.Binary
