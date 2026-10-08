module

public import ArithLemmas.Mathlib.Rat.DenominatorArithmetic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Dyadic有理数の算術と共通分母（第4段階4E-5）

分母が2の冪である有理数について、標準の `ℚ` をそのまま使った表現述語を定める。
Mathlib の `Dyadic` 型を再定義せず、既存 `Rat` 層で使える閉性定理を導く。
原典：`OAI/GroupTheory/Thompson/DyadicArithmetic.lean` の算術的核。
-/

public section

namespace ArithLemmas.Mathlib.Rat

/-- 整数を２の冪で割る形で表せる有理数。 -/
@[expose] def IsDyadicRat (x : ℚ) : Prop :=
  ∃ (k : ℤ) (n : ℕ), x = (k : ℚ) / (2 : ℚ) ^ n

/-- 典型的な dyadic 有理数の表示。 -/
theorem isDyadicRat_div_pow (k : ℤ) (n : ℕ) :
    IsDyadicRat ((k : ℚ) / (2 : ℚ) ^ n) :=
  ⟨k, n, rfl⟩

/-- すべての整数は dyadic 有理数である。 -/
theorem isDyadicRat_intCast (k : ℤ) : IsDyadicRat (k : ℚ) := by
  exact ⟨k, 0, by simp⟩

/-- 自然数も dyadic 有理数である。 -/
theorem isDyadicRat_natCast (k : ℕ) : IsDyadicRat (k : ℚ) := by
  simpa only [Int.cast_natCast] using isDyadicRat_intCast (k : ℤ)

/-- dyadic 有理数は符号反転に閉じる。 -/
theorem isDyadicRat_neg {x : ℚ} (hx : IsDyadicRat x) :
    IsDyadicRat (-x) := by
  obtain ⟨k, n, hk⟩ := hx
  refine ⟨-k, n, ?_⟩
  rw [hk]
  simp only [Int.cast_neg, neg_div]

/-- dyadic 有理数は積に閉じる。 -/
theorem isDyadicRat_mul {x y : ℚ}
    (hx : IsDyadicRat x) (hy : IsDyadicRat y) :
    IsDyadicRat (x * y) := by
  obtain ⟨k, n, hk⟩ := hx
  obtain ⟨l, m, hl⟩ := hy
  refine ⟨k * l, n + m, ?_⟩
  rw [hk, hl]
  simp only [Int.cast_mul, pow_add, div_mul_div_comm]

/-- dyadic 有理数は和に閉じる。 -/
theorem isDyadicRat_add {x y : ℚ}
    (hx : IsDyadicRat x) (hy : IsDyadicRat y) :
    IsDyadicRat (x + y) := by
  obtain ⟨k, n, hk⟩ := hx
  obtain ⟨l, m, hl⟩ := hy
  refine ⟨k * 2 ^ m + l * 2 ^ n, n + m, ?_⟩
  rw [hk, hl]
  push_cast
  rw [pow_add]
  field_simp

/-- dyadic 有理数は差に閉じる。 -/
theorem isDyadicRat_sub {x y : ℚ}
    (hx : IsDyadicRat x) (hy : IsDyadicRat y) :
    IsDyadicRat (x - y) := by
  simpa only [sub_eq_add_neg] using isDyadicRat_add hx (isDyadicRat_neg hy)

/-- 共通分母の指数を増やしても値は変わらない。 -/
theorem dyadicRat_raise_denominator {x : ℚ} {n : ℕ}
    (hx : ∃ k : ℤ, x = (k : ℚ) / (2 : ℚ) ^ n) (m : ℕ) :
    ∃ k : ℤ, x = (k : ℚ) / (2 : ℚ) ^ (n + m) := by
  obtain ⟨k, rfl⟩ := hx
  refine ⟨k * 2 ^ m, ?_⟩
  push_cast
  rw [pow_add]
  field_simp

/-- 分母指数の単調拡大。 -/
theorem dyadicRat_denominator_mono {x : ℚ} {n N : ℕ}
    (hx : ∃ k : ℤ, x = (k : ℚ) / (2 : ℚ) ^ n)
    (hn : n ≤ N) :
    ∃ k : ℤ, x = (k : ℚ) / (2 : ℚ) ^ N := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact dyadicRat_raise_denominator hx m

/-- 任意の有限dyadic有理数族には２の冪という共通分母が存在する。 -/
theorem dyadicRat_common_denominator_finset {ι : Type*}
    (s : Finset ι) (f : ι → ℚ)
    (hs : ∀ i ∈ s, IsDyadicRat (f i)) :
    ∃ n : ℕ, ∀ i ∈ s, ∃ k : ℤ, f i = (k : ℚ) / (2 : ℚ) ^ n := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨k, n, hn⟩ := hs i (Finset.mem_insert_self i s)
      obtain ⟨m, hm⟩ := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
      refine ⟨n + m, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact dyadicRat_raise_denominator ⟨k, hn⟩ m
      · simpa only [Nat.add_comm m n] using dyadicRat_raise_denominator (hm j hj) n

/-- 有限集合に含まれるdyadic有理数は同じ格子の上にある。 -/
theorem dyadicRat_common_denominator (s : Finset ℚ)
    (hs : ∀ x ∈ s, IsDyadicRat x) :
    ∃ n : ℕ, ∀ x ∈ s, ∃ k : ℤ, x = (k : ℚ) / (2 : ℚ) ^ n :=
  dyadicRat_common_denominator_finset s id hs

/-- dyadic有理数の既約分母は２の冪を割る。 -/
theorem isDyadicRat_den_dvd_two_pow {x : ℚ} (hx : IsDyadicRat x) :
    ∃ n : ℕ, x.den ∣ 2 ^ n := by
  obtain ⟨k, n, hk⟩ := hx
  refine ⟨n, ?_⟩
  have hden : (((2 : ℚ) ^ n)⁻¹).den = (2 : ℕ) ^ n := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (Rat.inv_natCast_den_of_pos (pow_pos (by decide : 0 < (2 : ℕ)) n))
  have hmul := Rat.mul_den_dvd (k : ℚ) (((2 : ℚ) ^ n)⁻¹)
  rw [hk]
  simpa only [div_eq_mul_inv, Rat.den_intCast, one_mul, hden] using hmul

end ArithLemmas.Mathlib.Rat
