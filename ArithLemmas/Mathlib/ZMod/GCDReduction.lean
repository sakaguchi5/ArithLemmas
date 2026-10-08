module

public import ArithLemmas.Pure.Nat.GCD
public import ArithLemmas.Mathlib.ZMod.Basic
import Mathlib.Data.ZMod.Basic

/-!
# GCD縮約と剰余環（第3段階3C）

GCDを除いた縮約後の分子・法が互いに素であることから、
対応する剰余環の可逆性を導出する。Pure層からMathlibへの依存は追加しない。
原典：OAI/NumberTheory/EgyptianFractions/ReducedCharacter.lean の縮約算術。
-/

public section

namespace ArithLemmas.Mathlib.ZMod

open ArithLemmas.Pure.Defs.Nat

/-- 正の法を最大公約数で縮約しても正のままである。 -/
theorem gcdReducedModulus_pos (a u : Nat) (hu : 0 < u) :
    0 < u / Nat.gcd a u :=
  ArithLemmas.Pure.Nat.reduced_modulus_pos a u hu

/-- 分子と法を同じGCDで縮約すると、両者は互いに素となる。 -/
theorem gcdReduced_coprime (a u : Nat) (hu : 0 < u) :
    Nat.Coprime (a / Nat.gcd a u) (u / Nat.gcd a u) :=
  Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a hu)

/-- 縮約した分子は、縮約した法のZModにおいて単元である。 -/
theorem gcdReduced_isUnit (a u : Nat) (hu : 0 < u) :
    IsUnit (((a / Nat.gcd a u : Nat) : ZMod (u / Nat.gcd a u))) :=
  (ZMod.isUnit_iff_coprime _ _).2 (gcdReduced_coprime a u hu)

/-- 縮約された分子には剰余環上で乗法逆元が存在する。 -/
theorem gcdReduced_mul_inv (a u : Nat) (hu : 0 < u) :
    (((a / Nat.gcd a u : Nat) : ZMod (u / Nat.gcd a u))) *
      (((a / Nat.gcd a u : Nat) : ZMod (u / Nat.gcd a u)))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (gcdReduced_isUnit a u hu)

/-- GCD座標で書いた縮約分子にも可逆性が成立する。 -/
theorem gcdCoordinates_isUnit (a u : Nat) (hu : 0 < u) :
    IsUnit (((gcdCoordinates (a, u)).2.1 : ZMod (gcdCoordinates (a, u)).2.2)) := by
  exact gcdReduced_isUnit a u hu

/-- 縮約法における自然数の可逆性は、縮約法との互いに素性と同値。 -/
theorem gcdReduced_isUnit_iff (a u x : Nat) :
    IsUnit ((x : Nat) : ZMod (u / Nat.gcd a u)) ↔
      Nat.Coprime x (u / Nat.gcd a u) :=
  ZMod.isUnit_iff_coprime _ _

/-- 縮約法で二つの自然数が等しい剰余類を表す条件。 -/
theorem gcdReduced_natCast_eq_iff (a u x y : Nat) :
    (x : ZMod (u / Nat.gcd a u)) = (y : ZMod (u / Nat.gcd a u)) ↔
      x % (u / Nat.gcd a u) = y % (u / Nat.gcd a u) :=
  ZMod.natCast_eq_natCast_iff' x y (u / Nat.gcd a u)

end ArithLemmas.Mathlib.ZMod
