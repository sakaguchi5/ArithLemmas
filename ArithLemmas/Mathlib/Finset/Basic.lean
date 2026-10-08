module

public import Mathlib.Data.Nat.Count
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# 有限和で表した桁の値と剰余類の計数

有限和に関する汎用的な計算と、周期的な剰余類の個数を扱う。
原典：ハイルブロン三角形問題における桁の符号化。
-/
public section
set_option linter.style.docString false

namespace ArithLemmas.Mathlib.Finset

/-- 基数と桁列から、最初の指定個数の桁が表す自然数を作る。-/
@[expose] def baseValue (B k : ℕ) (digit : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range k, digit i * B ^ i

/-- 先頭の桁を取り出すと、残りの桁は基数倍として表せる。-/
theorem baseValue_succ (B k : ℕ) (digit : ℕ → ℕ) :
    baseValue B (k + 1) digit =
      digit 0 + B * baseValue B k (fun i => digit (i + 1)) := by
  unfold baseValue
  rw [Finset.sum_range_succ']
  simp only [pow_zero, mul_one, pow_succ, Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- 一桁以上の数を基数で割った余りは、先頭の桁の剰余に等しい。-/
theorem baseValue_mod (B k : ℕ) (digit : ℕ → ℕ) (hk : 0 < k) :
    baseValue B k digit % B = digit 0 % B := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [baseValue_succ]
  simp

/-- 基数より小さい剰余を与える自然数は、長さが基数の区間にちょうど一つ存在する。-/
theorem count_mod_period {r a : ℕ} (ha : a < r) :
    Nat.count (fun n => n % r = a) r = 1 := by
  rw [Nat.count_eq_card_filter_range]
  have hset : (Finset.range r).filter (fun n => n % r = a) = {a} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hn, he⟩
      simpa [Nat.mod_eq_of_lt hn] using he
    · rintro rfl
      exact ⟨ha, Nat.mod_eq_of_lt ha⟩
  rw [hset]
  simp

/-- 基数の整数倍の長さでは、指定した剰余がちょうどその倍数だけ現れる。-/
theorem count_mod_mul {r a : ℕ} (ha : a < r) (m : ℕ) :
    Nat.count (fun n => n % r = a) (r * m) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Nat.count_add, ih]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    rw [count_mod_period ha]

end ArithLemmas.Mathlib.Finset
