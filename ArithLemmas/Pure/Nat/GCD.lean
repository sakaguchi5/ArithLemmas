module

public import ArithLemmas.Pure.Nat.Basic
public import ArithLemmas.Pure.Defs.Nat.GCDCoordinates

/-!
# GCD・互除法・GCD座標の導出定理

既存の Pure の Euclid/GCD 定理を利用し、OpenAI数学証明群に現れる
問題に依存しない算術定理をLean本体の自然数定理から導く。

原典：Analysis/MatrixSigning/Arithmetic/BinaryGCD、
NumberTheory/EgyptianFractions/ReducedCharacter、
NumberTheory/Ostmann/Arithmetic/LcmFrequencySum、
NumberTheory/TwoPointCorrelations/MRTDivisorPairs。
-/

public section

namespace ArithLemmas.Pure.Nat

open ArithLemmas.Pure.Defs.Nat

/-- Euclid の互除法を二度行っても gcd は変わらない。
原典の `gcd_two_reductions` を自然数のみで導出する。 -/
theorem gcd_two_reductions (a b : Nat) :
    Nat.gcd a b = Nat.gcd (a % b) (b % (a % b)) := by
  calc
    Nat.gcd a b = Nat.gcd (a % b) b := by
      rw [Nat.gcd_comm a b, Nat.gcd_rec b a]
    _ = Nat.gcd (a % b) (b % (a % b)) := by
      rw [Nat.gcd_rec (a % b) b, Nat.gcd_comm]

/-- 正の法を gcd で縮約しても、商は正である。
原典の `reduced_modulus_pos` を Mathlib を用いず導出する。 -/
theorem reduced_modulus_pos (a u : Nat) (hu : 0 < u) :
    0 < u / Nat.gcd a u :=
  Nat.div_pos (Nat.gcd_le_right a hu) (Nat.gcd_pos_of_pos_right a hu)

/-- GCD座標の第一成分は、二数の最大公約数である。 -/
theorem gcdCoordinates_gcd (v : Nat × Nat) :
    (gcdCoordinates v).1 = Nat.gcd v.1 v.2 := rfl

/-- GCD座標から第一の自然数を復元する。 -/
theorem gcdCoordinates_recover_left (v : Nat × Nat) :
    (gcdCoordinates v).1 * (gcdCoordinates v).2.1 = v.1 := by
  change Nat.gcd v.1 v.2 * (v.1 / Nat.gcd v.1 v.2) = v.1
  simpa only [Nat.mul_comm] using Nat.div_mul_cancel (Nat.gcd_dvd_left v.1 v.2)

/-- GCD座標から第二の自然数を復元する。 -/
theorem gcdCoordinates_recover_right (v : Nat × Nat) :
    (gcdCoordinates v).1 * (gcdCoordinates v).2.2 = v.2 := by
  change Nat.gcd v.1 v.2 * (v.2 / Nat.gcd v.1 v.2) = v.2
  simpa only [Nat.mul_comm] using Nat.div_mul_cancel (Nat.gcd_dvd_right v.1 v.2)

/-- GCD座標から二つの入力を同時に復元する。 -/
theorem gcdCoordinates_recover (v : Nat × Nat) :
    (gcdCoordinates v).1 * (gcdCoordinates v).2.1 = v.1 ∧
    (gcdCoordinates v).1 * (gcdCoordinates v).2.2 = v.2 :=
  ⟨gcdCoordinates_recover_left v, gcdCoordinates_recover_right v⟩

/-- 入力を両方復元できるため、GCD座標への写像は単射である。 -/
theorem gcdCoordinates_injective : Function.Injective gcdCoordinates := by
  intro x y h
  have hx := gcdCoordinates_recover x
  have hy := gcdCoordinates_recover y
  apply Prod.ext
  · exact hx.1.symm.trans
      ((congrArg (fun z : Nat × Nat × Nat => z.1 * z.2.1) h).trans hy.1)
  · exact hx.2.symm.trans
      ((congrArg (fun z : Nat × Nat × Nat => z.1 * z.2.2) h).trans hy.2)

/-- GCD座標の第一成分は、第一の元の自然数を割り切る。 -/
theorem gcdCoordinates_dvd_left (v : Nat × Nat) :
    (gcdCoordinates v).1 ∣ v.1 :=
  Nat.gcd_dvd_left v.1 v.2

/-- GCD座標の第一成分は、第二の元の自然数を割り切る。 -/
theorem gcdCoordinates_dvd_right (v : Nat × Nat) :
    (gcdCoordinates v).1 ∣ v.2 :=
  Nat.gcd_dvd_right v.1 v.2

/-- 二つのGCD座標が等しいことは、元の自然数対が等しいことと同値である。 -/
theorem gcdCoordinates_eq_iff {v w : Nat × Nat} :
    gcdCoordinates v = gcdCoordinates w ↔ v = w := by
  constructor
  · intro h
    exact gcdCoordinates_injective h
  · intro h
    exact congrArg gcdCoordinates h

/-- 頻度座標の復元定理：二成分とも元の値に戻る。 -/
theorem gcdFrequencyCoordinates_recover (v : Nat × Nat) :
    (gcdFrequencyCoordinates v).1 * (gcdFrequencyCoordinates v).2.1 = v.1 ∧
    (gcdFrequencyCoordinates v).1 * (gcdFrequencyCoordinates v).2.2 = v.2 :=
  gcdCoordinates_recover v

/-- 頻度座標への変換は単射である。 -/
theorem gcdFrequencyCoordinates_injective :
    Function.Injective gcdFrequencyCoordinates := gcdCoordinates_injective

/-- MRT GCD三つ組の左側の成分から入力を復元する。 -/
theorem mrt_gcd_triple_left (v : Nat × Nat) :
    (mrtGcdTriple v).1 * (mrtGcdTriple v).2.1 = v.1 :=
  gcdCoordinates_recover_left v

/-- MRT GCD三つ組の右側の成分から入力を復元する。 -/
theorem mrt_gcd_triple_right (v : Nat × Nat) :
    (mrtGcdTriple v).1 * (mrtGcdTriple v).2.2 = v.2 :=
  gcdCoordinates_recover_right v

/-- MRT GCD三つ組への写像は単射である。 -/
theorem mrt_gcd_triple_injective : Function.Injective mrtGcdTriple :=
  gcdCoordinates_injective

/-- 第一成分が正なら、GCD座標の共通因子は第一成分以下である。 -/
theorem gcdCoordinates_gcd_le_left {a b : Nat} (ha : 0 < a) :
    (gcdCoordinates (a, b)).1 ≤ a :=
  Nat.gcd_le_left b ha

/-- 第二成分が正なら、GCD座標の共通因子は第二成分以下である。 -/
theorem gcdCoordinates_gcd_le_right {a b : Nat} (hb : 0 < b) :
    (gcdCoordinates (a, b)).1 ≤ b :=
  Nat.gcd_le_right a hb

/-- 左側の縮約商は元の自然数を超えない。 -/
theorem gcdCoordinates_left_quotient_le (v : Nat × Nat) :
    (gcdCoordinates v).2.1 ≤ v.1 :=
  Nat.div_le_self v.1 (Nat.gcd v.1 v.2)

/-- 右側の縮約商は元の自然数を超えない。 -/
theorem gcdCoordinates_right_quotient_le (v : Nat × Nat) :
    (gcdCoordinates v).2.2 ≤ v.2 :=
  Nat.div_le_self v.2 (Nat.gcd v.1 v.2)

/-- 左側の自然数が正なら、GCD座標の共通因子も正である。 -/
theorem gcdCoordinates_pos_of_left {a b : Nat} (ha : 0 < a) :
    0 < (gcdCoordinates (a, b)).1 :=
  Nat.gcd_pos_of_pos_left b ha

/-- 右側の自然数が正なら、GCD座標の共通因子も正である。 -/
theorem gcdCoordinates_pos_of_right {a b : Nat} (hb : 0 < b) :
    0 < (gcdCoordinates (a, b)).1 :=
  Nat.gcd_pos_of_pos_right a hb

/-- 正の左成分は共通因子で割っても正のままである。 -/
theorem gcdCoordinates_left_quotient_pos {a b : Nat} (ha : 0 < a) :
    0 < (gcdCoordinates (a, b)).2.1 :=
  Nat.div_pos (Nat.gcd_le_left b ha) (Nat.gcd_pos_of_pos_left b ha)

/-- 正の右成分は共通因子で割っても正のままである。 -/
theorem gcdCoordinates_right_quotient_pos {a b : Nat} (hb : 0 < b) :
    0 < (gcdCoordinates (a, b)).2.2 :=
  reduced_modulus_pos a b hb

end ArithLemmas.Pure.Nat
