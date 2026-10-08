module

public import ArithLemmas.Mathlib.Nat.PrimeDivisors
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorization.Basic
/-!
# 有限素数積と最大公約数（第4段階4E-1）

有限集合上の素数の積と自然数の最大公約数を、法を割り切る素数だけで評価する。
第4段階4D の素因数・約数 API を再利用し、定義の追加なしに導出定理を構築する。

原典：OpenAI `OAI/NumberTheory/EgyptianFractions/PrimeHits.lean`
固定原典：`adc7f1241b42e322a6451854ab7e4b4c146bf78a`
v1.8 ID：81、31、82、83、84。追加した `prime_hits_*` は本ライブラリの導出定理。
-/

public section

namespace ArithLemmas.Mathlib.Nat

/-- 有限積との最大公約数は、各因子との最大公約数の積を割り切る。
原典 `gcd_prod_dvd_prod_gcd`（ID 81）。 -/
theorem gcd_prod_dvd_prod_gcd {ι : Type*} (s : Finset ι) (p : ι → ℕ) (u : ℕ) :
    Nat.gcd (∏ i ∈ s, p i) u ∣ ∏ i ∈ s, Nat.gcd (p i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have h : Nat.gcd (p i * ∏ j ∈ s, p j) u ∣
          Nat.gcd (p i) u * Nat.gcd (∏ j ∈ s, p j) u := by
        simpa only [gcd_eq_nat_gcd, Nat.gcd_comm] using
          (gcd_mul_dvd_mul_gcd u (p i) (∏ j ∈ s, p j))
      exact h.trans (Nat.mul_dvd_mul_left _ ih)

/-- 素数の有限積と法の最大公約数は、法を割り切る因子の積を割り切る。
同じ素数が複数回現れても成立する。原典ID 31。 -/
theorem gcd_prime_product_dvd_hits {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u : ℕ) (hp : ∀ i ∈ s, (p i).Prime) :
    Nat.gcd (∏ i ∈ s, p i) u ∣ ∏ i ∈ s.filter (fun i => p i ∣ u), p i := by
  classical
  have heq : (∏ i ∈ s, Nat.gcd (p i) u) =
      ∏ i ∈ s.filter (fun i => p i ∣ u), p i := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : p i ∣ u
    · simp [h, Nat.gcd_eq_left_iff_dvd.mpr h]
    · simp [h, ((hp i hi).coprime_iff_not_dvd.mpr h).gcd_eq_one]
  rw [← heq]
  exact gcd_prod_dvd_prod_gcd s p u

/-- 法を割り切る素数のヒット数から、有限素数積との gcd を冪で評価する。
原典ID 82。 -/
theorem gcd_prime_product_le_pow_hits {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u B : ℕ) (hp : ∀ i ∈ s, (p i).Prime) (hB : ∀ i ∈ s, p i ≤ B) :
    Nat.gcd (∏ i ∈ s, p i) u ≤ B ^ (s.filter (fun i => p i ∣ u)).card := by
  classical
  have hpos : 0 < ∏ i ∈ s.filter (fun i => p i ∣ u), p i := by
    apply Finset.prod_pos
    intro i hi
    exact (hp i (Finset.mem_filter.mp hi).1).pos
  apply (Nat.le_of_dvd hpos (gcd_prime_product_dvd_hits s p u hp)).trans
  apply Finset.prod_le_pow_card
  intro i hi
  exact hB i (Finset.mem_filter.mp hi).1

/-- 周波数因子を伴う素数積との gcd に対して、因子の大きさを使った上界を与える。
原典ID 83。 -/
theorem gcd_frequency_prime_product_le {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (u B l : ℕ) (hp : ∀ i ∈ s, (p i).Prime)
    (hB : ∀ i ∈ s, p i ≤ B) (hl : 0 < l) :
    Nat.gcd (l * ∏ i ∈ s, p i) u ≤ l * B ^ (s.filter (fun i => p i ∣ u)).card := by
  classical
  have hg : Nat.gcd (l * ∏ i ∈ s, p i) u ∣
      Nat.gcd l u * Nat.gcd (∏ i ∈ s, p i) u := by
    simpa only [gcd_eq_nat_gcd, Nat.gcd_comm] using
      gcd_mul_dvd_mul_gcd u l (∏ i ∈ s, p i)
  have hprod : 0 < ∏ i ∈ s, p i := Finset.prod_pos (fun i hi => (hp i hi).pos)
  have hpos : 0 < Nat.gcd l u * Nat.gcd (∏ i ∈ s, p i) u := by
    exact Nat.mul_pos (Nat.gcd_pos_of_pos_left u hl) (Nat.gcd_pos_of_pos_left u hprod)
  exact (Nat.le_of_dvd hpos hg).trans (Nat.mul_le_mul
    (Nat.gcd_le_left u hl) (gcd_prime_product_le_pow_hits s p u B hp hB))

/-- 素数集合から法を割り切る素数だけを選んだ集合は、法の素因数集合に含まれる。
既存の4D `prime_mem_primeFactors_iff_dvd` から導出する。 -/
theorem prime_hits_subset_primeFactors (P : Finset ℕ) (u : ℕ)
    (hu : 0 < u) (hp : ∀ p ∈ P, p.Prime) :
    P.filter (fun p => p ∣ u) ⊆ u.primeFactors := by
  intro p h
  obtain ⟨hpP, hpu⟩ := Finset.mem_filter.mp h
  exact (prime_mem_primeFactors_iff_dvd u p hu.ne' (hp p hpP)).mpr hpu

/-- 法を割り切る素数のヒット数は、異なる素因数の総数以下である。 -/
theorem prime_hits_card_le_primeFactors (P : Finset ℕ) (u : ℕ)
    (hu : 0 < u) (hp : ∀ p ∈ P, p.Prime) :
    (P.filter (fun p => p ∣ u)).card ≤ u.primeFactors.card :=
  Finset.card_le_card (prime_hits_subset_primeFactors P u hu hp)

/-- ヒット数は約数の個数以下である。4Dの約数評価へ接続する。 -/
theorem prime_hits_card_le_divisors (P : Finset ℕ) (u : ℕ)
    (hu : 0 < u) (hp : ∀ p ∈ P, p.Prime) :
    (P.filter (fun p => p ∣ u)).card ≤ u.divisors.card :=
  (prime_hits_card_le_primeFactors P u hu hp).trans (primeFactors_card_le_divisors_card u)

/-- 異なる素因数の集合について、下限 `L` の冪が法 `u` 以下となる。
原典ID 84。 -/
theorem prime_divisor_population_pow_le (P : Finset ℕ) (u L : ℕ)
    (hu : 0 < u) (hp : ∀ p ∈ P, p.Prime) (hL : ∀ p ∈ P, L ≤ p) :
    L ^ (P.filter (fun p => p ∣ u)).card ≤ u := by
  have hsub : P.filter (fun p => p ∣ u) ⊆ u.primeFactors :=
    prime_hits_subset_primeFactors P u hu hp
  have hdvd : (∏ p ∈ P.filter (fun p => p ∣ u), p) ∣ u :=
    (Finset.prod_dvd_prod_of_subset _ _ id hsub).trans (Nat.prod_primeFactors_dvd u)
  calc
    L ^ (P.filter (fun p => p ∣ u)).card ≤
        ∏ p ∈ P.filter (fun p => p ∣ u), p := by
      apply Finset.pow_card_le_prod
      intro p h
      exact hL p (Finset.mem_filter.mp h).1
    _ ≤ u := Nat.le_of_dvd hu hdvd

end ArithLemmas.Mathlib.Nat
