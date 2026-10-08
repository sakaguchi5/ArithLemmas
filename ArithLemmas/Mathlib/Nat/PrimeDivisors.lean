module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Finset.NatDivisors

/-!
# 素因数・約数の有限集合（第4段階4D）

素因数の集合を正の約数集合へ埋め込む。素数の約数と、互いに素な積の
約数個数を既存Mathlibの正規定理から導出する。
原典群：`OAI/NumberTheory/Jacobsthal`、`OAI/NumberTheory/OrdinaryCorrelations`。
-/

public section

namespace ArithLemmas.Mathlib.Nat

/-- 素因数は必ず元の自然数の約数である。 -/
theorem primeFactors_subset_divisors (n : ℕ) :
    n.primeFactors ⊆ n.divisors := by
  rw [Nat.primeFactors_eq_to_filter_divisors_prime]
  exact Finset.filter_subset _ _

/-- ０でない自然数に対し、素数が素因数であることと割り切ることは同値。 -/
theorem prime_mem_primeFactors_iff_dvd (n p : ℕ) (hn : n ≠ 0) (hp : p.Prime) :
    p ∈ n.primeFactors ↔ p ∣ n := by
  rw [Nat.primeFactors_eq_to_filter_divisors_prime]
  simp [Nat.mem_divisors, hn, hp]

/-- 異なる素因数の個数は約数の個数以下である。 -/
theorem primeFactors_card_le_divisors_card (n : ℕ) :
    n.primeFactors.card ≤ n.divisors.card :=
  Finset.card_le_card (primeFactors_subset_divisors n)

/-- 異なる素因数の個数は元の自然数以下である。 -/
theorem primeFactors_card_le_self (n : ℕ) :
    n.primeFactors.card ≤ n :=
  (primeFactors_card_le_divisors_card n).trans (Nat.card_divisors_le_self n)

/-- 素数の正の約数は１と素数自身のちょうど二つである。 -/
theorem prime_divisors_card (p : ℕ) (hp : p.Prime) :
    p.divisors.card = 2 := by
  rw [hp.divisors]
  simp [hp.ne_one.symm]

/-- 互いに素な二数の積の約数個数は、それぞれの約数個数の積に等しい。 -/
theorem coprime_divisors_card_mul (m n : ℕ) (h : m.Coprime n) :
    (m * n).divisors.card = m.divisors.card * n.divisors.card := by
  rw [h.divisors_mul, Finset.card_map, Finset.card_attach, Finset.card_product]

/-- 素数と互いに素な自然数の積では、約数個数がちょうど二倍になる。 -/
theorem prime_mul_divisors_card (p n : ℕ) (hp : p.Prime) (h : p.Coprime n) :
    (p * n).divisors.card = 2 * n.divisors.card := by
  rw [coprime_divisors_card_mul p n h, prime_divisors_card p hp]

end ArithLemmas.Mathlib.Nat
