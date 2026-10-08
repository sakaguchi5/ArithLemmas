module

/-!
# GCD座標の薄い定義

二つの自然数を、最大公約数と二つの縮約商で表す。
OAIの `gcdCoordinates`・`gcdFrequencyCoordinates`・`mrtGcdTriple`
は組の括弧構造も含め同じ情報を表すため、一つの定義と二つの別名に統合する。
原典：Ostmann/FrequencyLCM、Ostmann/LcmFrequencySum、TwoPointCorrelations/MRTDivisorPairs。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Nat

/-- 自然数対を、gcd とそれぞれを gcd で割った商からなる三つ組に変換する。 -/
def gcdCoordinates (v : Nat × Nat) : Nat × Nat × Nat :=
  (Nat.gcd v.1 v.2, v.1 / Nat.gcd v.1 v.2, v.2 / Nat.gcd v.1 v.2)

/-- Ostmann の頻度座標に由来する名称。`gcdCoordinates` と同じ定義を共有する。 -/
abbrev gcdFrequencyCoordinates (v : Nat × Nat) : Nat × Nat × Nat := gcdCoordinates v

/-- 二点相関に由来する名称。新たな構造を作らず既存の GCD 座標へ写す。 -/
abbrev mrtGcdTriple (v : Nat × Nat) : Nat × (Nat × Nat) := gcdCoordinates v

end ArithLemmas.Pure.Defs.Nat
