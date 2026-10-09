module

public import ArithLemmas.Mathlib.Finset.Basic
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Fintype.Pi

/-!
# 任意基数による位取り表現：値の上界・復元・一意性

既存の `baseValue` は、下位桁を先に並べて値を計算する有限和である。
正の基数 `B` に対し、`B` 未満の桁を `k` 個並べた表現は、
区間 `[0, B^k)` の整数と一対一に対応する。
`k` 桁より後ろの値は、この対応には影響しない。
したがって、この結果は二進数に限らず任意の正の基数に適用できる。
-/

public section

namespace ArithLemmas.Mathlib.Finset

/-- 先頭の桁が基数未満なら、位取り表現の値を基数で割ると
ちょうど先頭の一桁が取り除かれる。 -/
theorem baseValue_div_base (B k : ℕ) (f : ℕ → ℕ)
    (hB : 0 < B) (h0 : f 0 < B) :
    baseValue B (k + 1) f / B =
      baseValue B k (fun i => f (i + 1)) := by
  rw [baseValue_succ]
  rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h0, zero_add]

/-- 各桁が `B` 未満である `k` 桁の値は、必ず `B^k` 未満となる。
`B = 0` の場合も成立する。 -/
theorem baseValue_lt_pow (B : ℕ) :
    ∀ k (f : ℕ → ℕ),
      (∀ i, i < k → f i < B) → baseValue B k f < B ^ k := by
  intro k
  induction k with
  | zero =>
      intro f hf
      simp [baseValue]
  | succ k ih =>
      intro f hf
      have h0 : f 0 < B := hf 0 (Nat.zero_lt_succ k)
      have ht : baseValue B k (fun i => f (i + 1)) < B ^ k := by
        apply ih
        intro i hi
        exact hf (i + 1) (Nat.succ_lt_succ hi)
      rw [baseValue_succ, pow_succ]
      have hstep : f 0 + B * baseValue B k (fun i => f (i + 1)) <
          B * (baseValue B k (fun i => f (i + 1)) + 1) := by
        rw [Nat.mul_succ]
        omega
      calc
        f 0 + B * baseValue B k (fun i => f (i + 1)) <
            B * (baseValue B k (fun i => f (i + 1)) + 1) := hstep
        _ ≤ B * B ^ k := Nat.mul_le_mul_left B (Nat.succ_le_of_lt ht)
        _ = B ^ k * B := mul_comm _ _

/-- 各桁が基数未満である有限桁列は、その表現する値から一意に定まる。 -/
theorem baseValue_unique (B : ℕ) (hB : 0 < B) :
    ∀ k (f g : ℕ → ℕ),
      (∀ i, i < k → f i < B) →
      (∀ i, i < k → g i < B) →
      baseValue B k f = baseValue B k g →
      ∀ i, i < k → f i = g i := by
  intro k
  induction k with
  | zero =>
      intro f g hf hg he i hi
      omega
  | succ k ih =>
      intro f g hf hg he i hi
      have h0f : f 0 < B := hf 0 (Nat.zero_lt_succ k)
      have h0g : g 0 < B := hg 0 (Nat.zero_lt_succ k)
      have hhead : f 0 = g 0 := by
        have hmod := congrArg (fun v : ℕ => v % B) he
        rw [baseValue_mod B (k + 1) f (Nat.zero_lt_succ k),
          baseValue_mod B (k + 1) g (Nat.zero_lt_succ k),
          Nat.mod_eq_of_lt h0f, Nat.mod_eq_of_lt h0g] at hmod
        exact hmod
      have htail : baseValue B k (fun j => f (j + 1)) =
          baseValue B k (fun j => g (j + 1)) := by
        have hdiv := congrArg (fun v : ℕ => v / B) he
        rwa [baseValue_div_base B k f hB h0f,
          baseValue_div_base B k g hB h0g] at hdiv
      cases i with
      | zero => exact hhead
      | succ j =>
          have hj : j < k := Nat.lt_of_succ_lt_succ hi
          exact ih (fun t => f (t + 1)) (fun t => g (t + 1))
            (fun t ht => hf (t + 1) (Nat.succ_lt_succ ht))
            (fun t ht => hg (t + 1) (Nat.succ_lt_succ ht))
            htail j hj

/-- `B^k` 未満の自然数はすべて、基数 `B` で `k` 桁の表現を持つ。
除算の商と余りを順に用いて、各桁を構成する。 -/
theorem baseValue_exists_of_lt_pow (B : ℕ) (hB : 0 < B) :
    ∀ k (n : ℕ), n < B ^ k →
      ∃ f : ℕ → ℕ,
        (∀ i, i < k → f i < B) ∧ baseValue B k f = n := by
  intro k
  induction k with
  | zero =>
      intro n hn
      have hn0 : n = 0 := by simpa only [pow_zero, Nat.lt_one_iff] using hn
      refine ⟨fun _ => 0, ?_, ?_⟩
      · intro i hi
        omega
      · simp [baseValue, hn0]
  | succ k ih =>
      intro n hn
      have htail : n / B < B ^ k := by
        apply (Nat.div_lt_iff_lt_mul hB).mpr
        simpa only [pow_succ] using hn
      obtain ⟨d, hd, hdval⟩ := ih (n / B) htail
      refine ⟨fun i => if i = 0 then n % B else d (i - 1), ?_, ?_⟩
      · intro i hi
        cases i with
        | zero => simpa using Nat.mod_lt n hB
        | succ i =>
            simpa using hd i (Nat.lt_of_succ_lt_succ hi)
      · rw [baseValue_succ]
        have heq : (fun i =>
            (if i + 1 = 0 then n % B else d (i + 1 - 1))) = d := by
          funext i
          simp
        rw [heq, hdval]
        exact Nat.mod_add_div n B

/-- **有限桁表現の完全性。** 自然数が区間 `[0, B^k)` に属することと、
`B` 未満の `k` 個の桁で表せることは同値である。
さらに、その範囲の桁は一意である。 -/
theorem baseValue_exists_iff_lt_pow (B k n : ℕ) (hB : 0 < B) :
    (∃ f : ℕ → ℕ,
      (∀ i, i < k → f i < B) ∧ baseValue B k f = n) ↔
      n < B ^ k := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact baseValue_lt_pow B k f hf
  · exact baseValue_exists_of_lt_pow B hB k n

/-- 基数 `B` 未満の桁からなる二つの表現の値が等しいことと、
指定された `k` 個のすべての桁が等しいことは同値である。 -/
theorem baseValue_eq_iff_digits (B k : ℕ) (f g : ℕ → ℕ)
    (hB : 0 < B)
    (hf : ∀ i, i < k → f i < B)
    (hg : ∀ i, i < k → g i < B) :
    baseValue B k f = baseValue B k g ↔
      ∀ i, i < k → f i = g i := by
  constructor
  · exact baseValue_unique B hB k f g hf hg
  · intro h
    unfold baseValue
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i (Finset.mem_range.mp hi)]


/-- 基数 `B` 未満の `k` 個の桁と、区間 `[0, B^k)` の整数との
明示的な同値写像。 -/
noncomputable def baseValueEquivFin (B k : ℕ) (hB : 0 < B) :
    (Fin k → Fin B) ≃ Fin (B ^ k) := by
  classical
  let encode (x : Fin k → Fin B) : Fin (B ^ k) :=
    ⟨baseValue B k (fun i => if hi : i < k then (x ⟨i, hi⟩).val else 0),
      baseValue_lt_pow B k _ (by
        intro i hi
        simp only [dite_eq_left hi]
        exact (x ⟨i, hi⟩).isLt)⟩
  refine Equiv.ofBijective encode ⟨?_, ?_⟩
  · intro x y hxy
    funext i
    apply Fin.ext
    have heq :
        baseValue B k (fun j => if hj : j < k then (x ⟨j, hj⟩).val else 0) =
        baseValue B k (fun j => if hj : j < k then (y ⟨j, hj⟩).val else 0) :=
      congrArg Fin.val hxy
    have hd := baseValue_unique B hB k
      (fun j => if hj : j < k then (x ⟨j, hj⟩).val else 0)
      (fun j => if hj : j < k then (y ⟨j, hj⟩).val else 0)
      (by intro j hj; simp only [dite_eq_left hj]; exact (x ⟨j, hj⟩).isLt)
      (by intro j hj; simp only [dite_eq_left hj]; exact (y ⟨j, hj⟩).isLt)
      heq i.val i.isLt
    simpa only [dite_eq_left i.isLt] using hd
  · intro y
    obtain ⟨f, hf, hval⟩ := baseValue_exists_of_lt_pow B hB k y.val y.isLt
    let x : Fin k → Fin B := fun i => ⟨f i.val, hf i.val i.isLt⟩
    refine ⟨x, Fin.ext ?_⟩
    change baseValue B k (fun i => if hi : i < k then (x ⟨i, hi⟩).val else 0) = y.val
    rw [← hval]
    unfold baseValue
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < k := Finset.mem_range.mp hi
    simp only [dite_eq_left hi', x]

/-- `k` 桁の有限桁ベクトル全体の濃度は、基数 `B` の
基本区間 `[0, B^k)` の要素数に一致する。 -/
theorem card_baseDigitVectors (B k : ℕ) (hB : 0 < B) :
    Fintype.card (Fin k → Fin B) = B ^ k := by
  classical
  calc
    Fintype.card (Fin k → Fin B) = Fintype.card (Fin (B ^ k)) :=
      Fintype.card_congr (baseValueEquivFin B k hB)
    _ = B ^ k := Fintype.card_fin (B ^ k)

end ArithLemmas.Mathlib.Finset
