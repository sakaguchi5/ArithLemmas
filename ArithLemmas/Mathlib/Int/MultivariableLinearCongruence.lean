module

public import ArithLemmas.Mathlib.Int.LinearCongruence
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.Algebra.EuclideanDomain.Int

/-!
# 多変数一次合同式：有限 GCD による可解性

有限和 `∑ i ∈ s, a i * x i` に対する整数一次合同式を扱う。
法 `m : ℕ` は `0` も許す。有限 GCD は整数係数の GCD と `m` の
GCD として定める。核心の十分性には Mathlib の有限 Bézout 恒等式
`Finset.gcd_eq_sum_mul` を用いる。
-/

public section

namespace ArithLemmas.Mathlib.Int

variable {ι : Type*}

/-- 有限個の整数変数についての線形形式。 -/
@[expose] def multivariableLinearForm (s : Finset ι) (a x : ι → ℤ) : ℤ :=
  ∑ i ∈ s, a i * x i

/-- 法とすべての係数の最大公約数。空族では `m`、法が `0` なら係数の GCD。 -/
@[expose] def multivariableLinearGCD (s : Finset ι) (a : ι → ℤ) (m : ℕ) : ℕ :=
  Int.gcd (m : ℤ) (s.gcd a)

/-- 有限線形形式は、変数の和を線形形式の和へ写す。 -/
theorem multivariableLinearForm_add (s : Finset ι) (a x y : ι → ℤ) :
    multivariableLinearForm s a (fun i => x i + y i) =
      multivariableLinearForm s a x + multivariableLinearForm s a y := by
  classical
  simp [multivariableLinearForm, mul_add, Finset.sum_add_distrib]

/-- 有限線形形式は、変数の差を線形形式の差へ写す。 -/
theorem multivariableLinearForm_sub (s : Finset ι) (a x y : ι → ℤ) :
    multivariableLinearForm s a (fun i => x i - y i) =
      multivariableLinearForm s a x - multivariableLinearForm s a y := by
  classical
  simp [multivariableLinearForm, mul_sub, Finset.sum_sub_distrib]

/-- 多変数一次合同式の可解性を有限 GCD の整除性で完全に特徴付ける。 -/
theorem multivariableLinearCongruence_exists_iff_gcd_dvd
    (s : Finset ι) (a : ι → ℤ) (b : ℤ) (m : ℕ) :
    (∃ x : ι → ℤ,
        multivariableLinearForm s a x ≡ b [ZMOD (m : ℤ)]) ↔
      (multivariableLinearGCD s a m : ℤ) ∣ b := by
  classical
  let g : ℕ := multivariableLinearGCD s a m
  have hgm : (g : ℤ) ∣ (m : ℤ) := by
    exact Int.gcd_dvd_left (m : ℤ) (s.gcd a)
  have hga : (g : ℤ) ∣ s.gcd a := by
    exact Int.gcd_dvd_right (m : ℤ) (s.gcd a)
  constructor
  · rintro ⟨x, hx⟩
    have hd : (m : ℤ) ∣ b - multivariableLinearForm s a x :=
      Int.modEq_iff_dvd.mp hx
    have hsum : (g : ℤ) ∣ multivariableLinearForm s a x := by
      apply Finset.dvd_sum
      intro i hi
      exact (hga.trans (Finset.gcd_dvd hi)).mul_right (x i)
    have hb : (g : ℤ) ∣
        (b - multivariableLinearForm s a x) +
          multivariableLinearForm s a x :=
      dvd_add (hgm.trans hd) hsum
    simpa only [sub_add_cancel] using hb
  · intro hb
    obtain ⟨k, hk⟩ := hb
    obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul s a
    let A : ℤ := Int.gcdA (m : ℤ) (s.gcd a)
    let B : ℤ := Int.gcdB (m : ℤ) (s.gcd a)
    have hbez : (g : ℤ) = (m : ℤ) * A + (s.gcd a) * B :=
      Int.gcd_eq_gcd_ab (m : ℤ) (s.gcd a)
    let x : ι → ℤ := fun i => f i * (B * k)
    have hsum : multivariableLinearForm s a x = (s.gcd a) * (B * k) := by
      calc
        multivariableLinearForm s a x =
            (∑ i ∈ s, a i * f i) * (B * k) := by
              unfold multivariableLinearForm x
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              ring
        _ = (s.gcd a) * (B * k) := by rw [← hf]
    have hb' : b = (m : ℤ) * (A * k) + (s.gcd a) * (B * k) := by
      calc
        b = (g : ℤ) * k := hk
        _ = _ := by rw [hbez]; ring
    refine ⟨x, Int.modEq_iff_dvd.mpr ?_⟩
    refine ⟨A * k, ?_⟩
    rw [hsum, hb']
    ring

/-- 既知解を原点に移すと、全解集合は同次合同式の解集合となる。 -/
theorem multivariableLinearCongruence_iff_homogeneous
    (s : Finset ι) (a c x : ι → ℤ) (b : ℤ) (m : ℕ)
    (hc : multivariableLinearForm s a c ≡ b [ZMOD (m : ℤ)]) :
    (multivariableLinearForm s a x ≡ b [ZMOD (m : ℤ)]) ↔
      multivariableLinearForm s a (fun i => x i - c i) ≡ 0
        [ZMOD (m : ℤ)] := by
  rw [multivariableLinearForm_sub]
  constructor
  · intro hx
    have h := hx.trans hc.symm
    simpa only [sub_self] using
      (Int.ModEq.sub_right (multivariableLinearForm s a c) h)
  · intro hx
    have h := Int.ModEq.add_right (multivariableLinearForm s a c) hx
    have hxc : multivariableLinearForm s a x ≡
        multivariableLinearForm s a c [ZMOD (m : ℤ)] := by
      simpa only [sub_add_cancel, zero_add] using h
    exact hxc.trans hc

end ArithLemmas.Mathlib.Int
