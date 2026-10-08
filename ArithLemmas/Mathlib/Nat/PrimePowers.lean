module

public import ArithLemmas.Mathlib.Nat.PrimeDivisors
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# 素数冪の約数・素因数指数（第4段階4E-5）

第4段階4Dの素因数・約数評価とMathlibの素数冪因数分解を結ぶ。
原典群：`OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean`、
`OAI/NumberTheory/TwoPoint` の素数冪算術、および Mathlib の正規定理。
-/

public section

namespace ArithLemmas.Mathlib.Nat

/-- 素数冪の正の約数は、０から指数までの冪にちょうど対応する。 -/
theorem prime_pow_divisors_eq (p k : ℕ) (hp : p.Prime) :
    (p ^ k).divisors = (Finset.range (k + 1)).map
      ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ :=
  Nat.divisors_prime_pow hp k

/-- 素数冪の正の約数の個数は指数プラス１である。 -/
theorem prime_pow_divisors_card (p k : ℕ) (hp : p.Prime) :
    (p ^ k).divisors.card = k + 1 := by
  rw [prime_pow_divisors_eq p k hp, Finset.card_map, Finset.card_range]

/-- 素数自身の冪に含まれる素数の指数は、冪の指数そのもの。 -/
theorem prime_pow_factorization_self (p k : ℕ) (hp : p.Prime) :
    (p ^ k).factorization p = k :=
  Nat.factorization_pow_self hp

/-- ゼロでない自然数の素数冪による整除を、素因数指数で判定する。 -/
theorem prime_pow_dvd_iff_factorization {p k n : ℕ}
    (hp : p.Prime) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p :=
  hp.pow_dvd_iff_le_factorization hn

/-- 素数冪が割り切るなら、その指数は素因数指数以下。 -/
theorem prime_pow_exponent_le_of_dvd {p k n : ℕ}
    (hp : p.Prime) (hn : n ≠ 0) (h : p ^ k ∣ n) :
    k ≤ n.factorization p :=
  (prime_pow_dvd_iff_factorization hp hn).mp h

/-- 素因数指数以下の冪は自然数を割り切る。 -/
theorem prime_pow_dvd_of_exponent_le {p k n : ℕ}
    (hp : p.Prime) (hn : n ≠ 0) (h : k ≤ n.factorization p) :
    p ^ k ∣ n :=
  (prime_pow_dvd_iff_factorization hp hn).mpr h

/-- 冪 `p^j` が `p^k` の約数であることは、指数の大小と同値。 -/
theorem prime_pow_mem_divisors_iff (p j k : ℕ) (hp : p.Prime) :
    p ^ j ∈ (p ^ k).divisors ↔ j ≤ k := by
  rw [Nat.mem_divisors_prime_pow hp]
  constructor
  · rintro ⟨i, hi, heq⟩
    have hji : j = i := (Nat.pow_right_injective hp.two_le) heq
    exact hji ▸ hi
  · intro hj
    exact ⟨j, hj, rfl⟩

/-- 互いに素な整数との積では、素数冪がもたらす約数個数係数は `k+1`。 -/
theorem prime_pow_coprime_divisors_card (p k n : ℕ)
    (hp : p.Prime) (h : (p ^ k).Coprime n) :
    (p ^ k * n).divisors.card = (k + 1) * n.divisors.card := by
  rw [coprime_divisors_card_mul (p ^ k) n h, prime_pow_divisors_card p k hp]

/-- 自然数の冪の正の約数個数は、その冪自身以下である。
`Nat.card_divisors_le_self` から導かれる系。 -/
theorem pow_divisors_card_le (n k : ℕ) :
    (n ^ k).divisors.card ≤ n ^ k := by
  exact Nat.card_divisors_le_self (n ^ k)

end ArithLemmas.Mathlib.Nat
