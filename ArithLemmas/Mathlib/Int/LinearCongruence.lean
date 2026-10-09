module

public import ArithLemmas.Mathlib.Int.GeneralizedCRT
public import Mathlib.Data.Int.GCD

/-!
# 一次合同式のGCD標準形

`m > 0` に対する `a*x ≡ b [ZMOD m]` は、`gcd(m,a) ∣ b` のとき、
法 `m / gcd(m,a)` の一つの合同類である。
Bézoutの等式とMathlibのGCD縮約補題を用い、余分な代表元定義を持たない。
-/

public section
namespace ArithLemmas.Mathlib.Int

/-- 一次合同式の解集合の正確な周期。`a = 0` でも定義できる。 -/
def linearCongruencePeriod (a : ℤ) (m : ℕ) : ℕ :=
  m / Int.gcd (m : ℤ) a

/-- 一次合同式は、係数と法のGCDが右辺を割り切るとき、かつそのときに限り解を持つ。 -/
theorem linearCongruence_exists_iff_gcd_dvd (a b : ℤ) (m : ℕ) :
    (∃ x : ℤ, a * x ≡ b [ZMOD (m : ℤ)]) ↔
      ((Int.gcd (m : ℤ) a : ℕ) : ℤ) ∣ b := by
  constructor
  · rintro ⟨x, hx⟩
    have hm : ((Int.gcd (m : ℤ) a : ℕ) : ℤ) ∣ (m : ℤ) :=
      Int.gcd_dvd_left (m : ℤ) a
    have ha : ((Int.gcd (m : ℤ) a : ℕ) : ℤ) ∣ a :=
      Int.gcd_dvd_right (m : ℤ) a
    have hsub : (m : ℤ) ∣ b - a * x := Int.modEq_iff_dvd.mp hx
    have h := dvd_add (dvd_mul_of_dvd_left ha x) (hm.trans hsub)
    convert h using 1
    ring
  · rintro ⟨t, ht⟩
    refine ⟨Int.gcdB (m : ℤ) a * t, Int.modEq_iff_dvd.mpr ?_⟩
    refine ⟨Int.gcdA (m : ℤ) a * t, ?_⟩
    calc
      b - a * (Int.gcdB (m : ℤ) a * t) =
          ((Int.gcd (m : ℤ) a : ℕ) : ℤ) * t -
            a * (Int.gcdB (m : ℤ) a * t) := by rw [ht]
      _ = (m : ℤ) * (Int.gcdA (m : ℤ) a * t) := by
          rw [Int.gcd_eq_gcd_ab]
          ring

/-- 正の法をGCDで割った後の周期も正。 -/
theorem linearCongruencePeriod_pos (a : ℤ) (m : ℕ) (hm : 0 < m) :
    0 < linearCongruencePeriod a m := by
  unfold linearCongruencePeriod
  have hd : Int.gcd (m : ℤ) a ∣ m :=
    Int.natCast_dvd_natCast.mp (Int.gcd_dvd_left (m : ℤ) a)
  have hle : Int.gcd (m : ℤ) a ≤ m := Nat.le_of_dvd hm hd
  have hg : 0 < Int.gcd (m : ℤ) a := by
    change 0 < Nat.gcd m a.natAbs
    exact Nat.gcd_pos_of_pos_left _ hm
  exact Nat.div_pos hle hg

/-- 既知の解を原点とする一次合同式の全解集合の特徴付け。 -/
theorem linearCongruence_iff_modEq (a b : ℤ) (m : ℕ) (hm : 0 < m)
    (c : ℤ) (hc : a * c ≡ b [ZMOD (m : ℤ)]) (x : ℤ) :
    (a * x ≡ b [ZMOD (m : ℤ)]) ↔
      x ≡ c [ZMOD (linearCongruencePeriod a m : ℤ)] := by
  constructor
  · intro hx
    have hmul : a * x ≡ a * c [ZMOD (m : ℤ)] := hx.trans hc.symm
    have hcancel := Int.ModEq.cancel_left_div_gcd
      (show (0 : ℤ) < m by exact_mod_cast hm) hmul
    simpa only [linearCongruencePeriod, Int.natCast_div] using hcancel
  · intro hx
    have hg : Int.gcd (m : ℤ) a ∣ m :=
      Int.natCast_dvd_natCast.mp (Int.gcd_dvd_left (m : ℤ) a)
    have hperiod :
        (((m / Int.gcd (m : ℤ) a : ℕ) : ℤ) *
          ((Int.gcd (m : ℤ) a : ℕ) : ℤ)) = (m : ℤ) := by
      exact_mod_cast Nat.div_mul_cancel hg
    have hdiff : ((m / Int.gcd (m : ℤ) a : ℕ) : ℤ) ∣ c - x :=
      Int.modEq_iff_dvd.mp hx
    have hcoef : ((Int.gcd (m : ℤ) a : ℕ) : ℤ) ∣ a :=
      Int.gcd_dvd_right (m : ℤ) a
    have hax : (m : ℤ) ∣ a * c - a * x := by
      rw [← hperiod]
      convert mul_dvd_mul hdiff hcoef using 1
      ring
    have hmod : a * x ≡ a * c [ZMOD (m : ℤ)] :=
      Int.modEq_iff_dvd.mpr hax
    exact hmod.trans hc

/-- 可解な一次合同式の全解集合は縮約周期の一つの剰余類。 -/
theorem linearCongruence_coset_iff_gcd_dvd (a b : ℤ) (m : ℕ) (hm : 0 < m) :
    (∃ c : ℤ, ∀ x : ℤ,
        (a * x ≡ b [ZMOD (m : ℤ)]) ↔
          x ≡ c [ZMOD (linearCongruencePeriod a m : ℤ)]) ↔
      ((Int.gcd (m : ℤ) a : ℕ) : ℤ) ∣ b := by
  constructor
  · rintro ⟨c, hc⟩
    exact (linearCongruence_exists_iff_gcd_dvd a b m).mp
      ⟨c, (hc c).mpr (Int.ModEq.refl c)⟩
  · intro h
    obtain ⟨c, hc⟩ := (linearCongruence_exists_iff_gcd_dvd a b m).mpr h
    exact ⟨c, fun x => linearCongruence_iff_modEq a b m hm c hc x⟩

/-- 同じ一次合同式の二解は、縮約周期を法として合同。 -/
theorem linearCongruence_unique_mod_period (a b : ℤ) (m : ℕ) (hm : 0 < m)
    (x y : ℤ) (hx : a * x ≡ b [ZMOD (m : ℤ)])
    (hy : a * y ≡ b [ZMOD (m : ℤ)]) :
    x ≡ y [ZMOD (linearCongruencePeriod a m : ℤ)] := by
  exact (linearCongruence_iff_modEq a b m hm y hy x).mp hx

end ArithLemmas.Mathlib.Int
