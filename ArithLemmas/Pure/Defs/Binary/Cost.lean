module

public import ArithLemmas.Pure.Defs.Binary.SignedDivision

/-!
# 二進除算のビット走査コストの薄い定義（第2段階2D）

比較・減算で走査するビット数を抽象的に計数する。
ランタイムの実測値ではなく、各段階のビット操作数を評価する数学的モデルである。
原典：OpenAI `OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`
（`bitScanCost`、`divisionIterations`、`divisionBitCost`、`signedDivisionBitCost`）。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Binary

/-- 二つのビット列を比較または減算する際の走査コスト。 -/
def bitScanCost : List Bool → List Bool → Nat
  | [], [] => 1
  | [], _ :: ys => bitScanCost [] ys + 1
  | _ :: xs, [] => bitScanCost xs [] + 1
  | _ :: xs, _ :: ys => bitScanCost xs ys + 1
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

/-- 二進除算で処理する被除数のビット数。 -/
def divisionIterations : List Bool → Nat
  | [] => 0
  | _ :: xs => divisionIterations xs + 1

/-- 二進長除算の走査コスト。
各桁の比較に加え、減算を行う場合は同じ長さの走査コストを加算する。 -/
def divisionBitCost (divisor : List Bool) : List Bool → Nat
  | [] => 1
  | b :: bs =>
      let qr := divideBits divisor bs
      let trial := b :: qr.2
      divisionBitCost divisor bs + 1 + bitScanCost trial divisor +
        if compareBits trial divisor = .lt then 0 else bitScanCost trial divisor

/-- 符号付き二進除算の走査コスト。
負数の場合は、余りの補正に必要な二つの減算の走査を加える。 -/
def signedDivisionBitCost (negative : Bool) (divisor xs : List Bool) : Nat :=
  divisionBitCost divisor xs +
    if negative then bitScanCost divisor [true] +
      bitScanCost (subtractBits divisor [true] false) (divideBits divisor xs).2
    else 0

end ArithLemmas.Pure.Defs.Binary
