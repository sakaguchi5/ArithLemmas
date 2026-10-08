module

public import ArithLemmas.Mathlib.Finset.Basic

/-!
# 自然数の完全周期における合同類計数（第4段階4B）

既存の `count_mod_mul` を有限集合の形へ移し、端数を付けた場合の上下界を導く。
原典：`OAI/Geometry/HeilbronnTriangle/DigitUnits.lean` などの周期計数。
-/

public section

namespace ArithLemmas.Mathlib.Finset

/-- `r * m` 個の自然数には、指定剰余 `a < r` が正確に `m` 個ある。 -/
theorem residue_range_card (r a m : ℕ) (ha : a < r) :
    ((Finset.range (r * m)).filter (fun n => n % r = a)).card = m := by
  rw [← Nat.count_eq_card_filter_range]
  exact count_mod_mul ha m

/-- 完全周期の後ろに任意の端数を付けても、出現回数は `m` から `m + t` の間。 -/
theorem residue_partial_count_bounds (r a m t : ℕ) (ha : a < r) :
    m ≤ Nat.count (fun n => n % r = a) (r * m + t) ∧
    Nat.count (fun n => n % r = a) (r * m + t) ≤ m + t := by
  have hcount : Nat.count (fun n => n % r = a) (r * m + t) =
      m + Nat.count (fun k => (r * m + k) % r = a) t := by
    rw [Nat.count_add, count_mod_mul ha m]
  rw [hcount]
  constructor
  · exact Nat.le_add_right _ _
  · exact Nat.add_le_add_left
      (Nat.count_le (p := fun k => (r * m + k) % r = a)) m

/-- 合同類の完全周期計数を自然数の `Finset` 記法で復元する。 -/
theorem residue_range_card_le (r a m : ℕ) (ha : a < r) :
    ((Finset.range (r * m)).filter (fun n => n % r = a)).card ≤ r * m := by
  rw [residue_range_card r a m ha]
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
  exact Nat.le_mul_of_pos_left m hr

end ArithLemmas.Mathlib.Finset
