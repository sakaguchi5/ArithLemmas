module

public import ArithLemmas.Pure.Nat.GCD
public import ArithLemmas.Mathlib.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.GCD.Basic

/-!
# GCD座標と有限集合（第3段階3B）

Pure層で証明済みのGCD座標の単射性と復元性を、有限集合・有限和に接続する。
ここでは新しいGCD座標の定義を作らず、Pure層の定義だけを再利用する。
原典：OAI/NumberTheory/Ostmann および TwoPointCorrelations の算術座標。
-/

public section

namespace ArithLemmas.Mathlib.Finset

open ArithLemmas.Pure.Defs.Nat
open ArithLemmas.Pure.Nat

/-- GCD座標の像は元の有限集合と同じ要素数を持つ。 -/
theorem gcdCoordinates_card_image (s : Finset (Nat × Nat)) :
    (s.image gcdCoordinates).card = s.card :=
  Finset.card_image_of_injective s gcdCoordinates_injective

/-- 頻度GCD座標への写像も有限集合の要素数を保存する。 -/
theorem gcdFrequencyCoordinates_card_image (s : Finset (Nat × Nat)) :
    (s.image gcdFrequencyCoordinates).card = s.card :=
  Finset.card_image_of_injective s gcdFrequencyCoordinates_injective

/-- MRT座標への写像も有限集合の要素数を保存する。 -/
theorem mrtGcdTriple_card_image (s : Finset (Nat × Nat)) :
    (s.image mrtGcdTriple).card = s.card :=
  Finset.card_image_of_injective s mrt_gcd_triple_injective

/-- 二つの有限集合の直積上でもGCD座標の像の要素数は積に等しい。 -/
theorem gcdCoordinates_card_product (s t : Finset Nat) :
    ((s.product t).image gcdCoordinates).card = s.card * t.card := by
  rw [gcdCoordinates_card_image]
  exact Finset.card_product s t

/-- GCD座標上の有限和を、元の自然数対上の有限和に引き戻す。 -/
theorem sum_gcdCoordinates_image (s : Finset (Nat × Nat))
    (f : Nat × Nat × Nat → Nat) :
    (∑ w ∈ s.image gcdCoordinates, f w) =
      ∑ v ∈ s, f (gcdCoordinates v) := by
  apply Finset.sum_image
  intro v hv w hw h
  exact gcdCoordinates_injective h

/-- GCD座標の第一成分の和は、各入力のGCDの和に一致する。 -/
theorem sum_gcdCoordinates_gcd (s : Finset (Nat × Nat)) :
    (∑ v ∈ s, (gcdCoordinates v).1) =
      ∑ v ∈ s, Nat.gcd v.1 v.2 := by
  apply Finset.sum_congr rfl
  intro v hv
  rfl

/-- GCD座標を使っても、各対の第一成分の有限和は復元できる。 -/
theorem sum_gcdCoordinates_recover_left (s : Finset (Nat × Nat)) :
    (∑ v ∈ s, (gcdCoordinates v).1 * (gcdCoordinates v).2.1) =
      ∑ v ∈ s, v.1 := by
  apply Finset.sum_congr rfl
  intro v hv
  exact gcdCoordinates_recover_left v

/-- GCD座標を使っても、各対の第二成分の有限和は復元できる。 -/
theorem sum_gcdCoordinates_recover_right (s : Finset (Nat × Nat)) :
    (∑ v ∈ s, (gcdCoordinates v).1 * (gcdCoordinates v).2.2) =
      ∑ v ∈ s, v.2 := by
  apply Finset.sum_congr rfl
  intro v hv
  exact gcdCoordinates_recover_right v

/-- GCD座標の共通因子とLCMの積は、元の二数の積に一致する。 -/
theorem gcdCoordinates_mul_lcm (a b : Nat) :
    (gcdCoordinates (a, b)).1 * Nat.lcm a b = a * b := by
  exact Nat.gcd_mul_lcm a b

end ArithLemmas.Mathlib.Finset
