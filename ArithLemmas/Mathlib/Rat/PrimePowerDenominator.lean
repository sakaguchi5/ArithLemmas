module

public import ArithLemmas.Mathlib.Rat.DyadicArithmetic
public import ArithLemmas.Mathlib.Nat.PrimePowers

/-!
# 素数冪と有理数の既約分母のBridge（第4段階4E-5）

分母の整除性に関する4E-5 Rat層と素数冪のNat層を接続する。
-/

public section

namespace ArithLemmas.Mathlib.Rat

/-- 素数冪の逆数の既約分母は素数冪そのものである。 -/
theorem prime_pow_reciprocal_den (p k : ℕ) (hp : p.Prime) :
    ((((p ^ k : ℕ) : ℚ)⁻¹)).den = p ^ k := by
  exact Rat.inv_natCast_den_of_pos (pow_pos hp.pos k)

/-- 素数冪の逆数との積の分母は、元の分母と素数冪の積を割る。 -/
theorem den_mul_prime_pow_reciprocal_dvd (a : ℚ) (p k : ℕ) (hp : p.Prime) :
    (a * (((p ^ k : ℕ) : ℚ)⁻¹)).den ∣ a.den * p ^ k := by
  simpa only [prime_pow_reciprocal_den p k hp] using
    (Rat.mul_den_dvd a (((p ^ k : ℕ) : ℚ)⁻¹))

/-- 素数冪の逆数の和の分母も、素数冪の積で統制できる。 -/
theorem den_add_prime_pow_reciprocals_dvd
    (p q k l : ℕ) (hp : p.Prime) (hq : q.Prime) :
    (((((p ^ k : ℕ) : ℚ)⁻¹) + (((q ^ l : ℕ) : ℚ)⁻¹))).den ∣
      p ^ k * q ^ l := by
  have ha : ((((p ^ k : ℕ) : ℚ)⁻¹)).den ∣ p ^ k * q ^ l := by
    rw [prime_pow_reciprocal_den p k hp]
    exact dvd_mul_right _ _
  have hb : ((((q ^ l : ℕ) : ℚ)⁻¹)).den ∣ p ^ k * q ^ l := by
    rw [prime_pow_reciprocal_den q l hq]
    exact dvd_mul_left _ _
  exact den_add_dvd_common ha hb

/-- 2の冪の逆数はDyadic有理数である。 -/
theorem isDyadicRat_inv_two_pow (k : ℕ) :
    IsDyadicRat (((2 : ℚ) ^ k)⁻¹) := by
  refine ⟨1, k, ?_⟩
  simp only [Int.cast_one, one_div]

end ArithLemmas.Mathlib.Rat
