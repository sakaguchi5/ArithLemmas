module

public import ArithLemmas.Pure.Nat.GCD
public import ArithLemmas.Mathlib.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.GCD.Basic

/-!
# GCD 標準形と有限集合

Pure で構成した `gcdCoordinatesEquiv` の単射性を使い、
有限集合の像と和に関する定理を導出する。
問題固有の同義座標の別名・別名ごとの定理は作らない。
-/

public section

namespace ArithLemmas.Mathlib.Finset

open ArithLemmas.Pure.Defs.Nat
open ArithLemmas.Pure.Nat

/-- GCD 標準座標への像の要素数は元と同じ。 -/
theorem gcdCoordinates_card_image (s : Finset (Nat × Nat)) :
    (s.image gcdCoordinates).card = s.card :=
  Finset.card_image_of_injective s gcdCoordinates_injective

/-- 直積を標準座標化した像の濃度は濃度の積。 -/
theorem gcdCoordinates_card_product (s t : Finset Nat) :
    ((s.product t).image gcdCoordinates).card = s.card * t.card := by
  rw [gcdCoordinates_card_image]
  exact Finset.card_product s t

/-- 標準座標上の任意の有限和は、元の対に沿って計算できる。 -/
theorem sum_gcdCoordinates_image (s : Finset (Nat × Nat))
    (f : Nat × Nat × Nat → Nat) :
    (∑ w ∈ s.image gcdCoordinates, f w) =
      ∑ v ∈ s, f (gcdCoordinates v) := by
  apply Finset.sum_image
  intro v hv w hw h
  exact gcdCoordinates_injective h

/-- GCD 座標上の共通因子の有限和。 -/
theorem sum_gcdCoordinates_gcd (s : Finset (Nat × Nat)) :
    (∑ v ∈ s, (gcdCoordinates v).1) =
      ∑ v ∈ s, Nat.gcd v.1 v.2 := by
  apply Finset.sum_congr rfl
  intro v hv
  rfl

/-- 左成分の有限和の復元。 -/
theorem sum_gcdCoordinates_recover_left (s : Finset (Nat × Nat)) :
    (∑ v ∈ s, (gcdCoordinates v).1 * (gcdCoordinates v).2.1) =
      ∑ v ∈ s, v.1 := by
  apply Finset.sum_congr rfl
  intro v hv
  exact gcdCoordinates_recover_left v

/-- 右成分の有限和の復元。 -/
theorem sum_gcdCoordinates_recover_right (s : Finset (Nat × Nat)) :
    (∑ v ∈ s, (gcdCoordinates v).1 * (gcdCoordinates v).2.2) =
      ∑ v ∈ s, v.2 := by
  apply Finset.sum_congr rfl
  intro v hv
  exact gcdCoordinates_recover_right v

/-- GCD と LCM の積による自然数対の積の再構成。 -/
theorem gcdCoordinates_mul_lcm (a b : Nat) :
    (gcdCoordinates (a, b)).1 * Nat.lcm a b = a * b := by
  exact Nat.gcd_mul_lcm a b

end ArithLemmas.Mathlib.Finset
