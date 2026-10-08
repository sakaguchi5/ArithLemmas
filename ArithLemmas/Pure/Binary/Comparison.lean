module

public import ArithLemmas.Pure.Binary.Representation
public import ArithLemmas.Pure.Defs.Binary.Comparison

/-!
# 二進比較の導出定理

比較結果が二つの二進列の数値的大小関係を表すことを証明する。
原典の `compareBits_correct` と `compareBits_lt_iff` を、Mathlib を使わない
Pure 層に移す。等号・大なり・反射性などのAPIを追加する。
原典：`OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`。
-/

public section

namespace ArithLemmas.Pure.Binary

open ArithLemmas.Pure.Defs.Binary

/-- １桁の比較結果は各桁の自然数としての値と一致する。 -/
theorem compareDigit_correct (a b : Bool) :
    OrderingCorrect (compareDigit a b) (digit a) (digit b) := by
  cases a <;> cases b <;>
    simp [OrderingCorrect, compareDigit, digit]

/-- 二進列の比較結果は、表す自然数の大小関係と一致する。 -/
theorem compareBits_correct (xs ys : List Bool) :
    OrderingCorrect (compareBits xs ys) (bitsValue xs) (bitsValue ys) := by
  induction xs generalizing ys with
  | nil =>
    induction ys with
    | nil => simp [compareBits, OrderingCorrect, bitsValue]
    | cons b bs ih =>
      cases hc : compareBits [] bs <;>
        simp only [hc, OrderingCorrect, bitsValue] at ih <;>
        cases b <;>
        simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega
  | cons a as ih =>
    cases ys with
    | nil =>
      have h := ih []
      cases hc : compareBits as [] <;>
        simp only [hc, OrderingCorrect, bitsValue] at h <;>
        cases a <;>
        simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega
    | cons b bs =>
      have h := ih bs
      cases hc : compareBits as bs <;>
        simp only [hc, OrderingCorrect] at h <;>
        cases a <;> cases b <;>
        simp [compareBits, hc, compareDigit, OrderingCorrect, bitsValue, digit] <;> omega

/-- 比較結果が `lt` であることと、左の数が右より小さいことは同値。 -/
theorem compareBits_lt_iff (xs ys : List Bool) :
    compareBits xs ys = .lt ↔ bitsValue xs < bitsValue ys := by
  have h := compareBits_correct xs ys
  cases hc : compareBits xs ys <;>
    simp [hc, OrderingCorrect] at h ⊢ <;> omega

/-- 比較結果が `eq` であることと、二進列の値が等しいことは同値。 -/
theorem compareBits_eq_iff (xs ys : List Bool) :
    compareBits xs ys = .eq ↔ bitsValue xs = bitsValue ys := by
  have h := compareBits_correct xs ys
  cases hc : compareBits xs ys <;>
    simp [hc, OrderingCorrect] at h ⊢ <;> omega

/-- 比較結果が `gt` であることと、右の数が左より小さいことは同値。 -/
theorem compareBits_gt_iff (xs ys : List Bool) :
    compareBits xs ys = .gt ↔ bitsValue ys < bitsValue xs := by
  have h := compareBits_correct xs ys
  cases hc : compareBits xs ys <;>
    simp [hc, OrderingCorrect] at h ⊢ <;> omega

/-- 比較結果が `gt` ではないことと、左の自然数が右以下であることは同値。 -/
theorem compareBits_le_iff (xs ys : List Bool) :
    compareBits xs ys ≠ .gt ↔ bitsValue xs ≤ bitsValue ys := by
  have h := compareBits_correct xs ys
  cases hc : compareBits xs ys <;>
    simp [hc, OrderingCorrect] at h ⊢ <;> omega

/-- 二進列は、自分自身と比較したとき必ず等しいと判定される。 -/
theorem compareBits_refl (xs : List Bool) : compareBits xs xs = .eq :=
  (compareBits_eq_iff xs xs).2 rfl

/-- 二進列の長さや表現が異なっても、同じ値なら等しいと判定される。 -/
theorem compareBits_eq_of_bitsValue_eq {xs ys : List Bool}
    (h : bitsValue xs = bitsValue ys) : compareBits xs ys = .eq :=
  (compareBits_eq_iff xs ys).2 h

/-- 左が右より小さいことは、引数を交換すると右が左より大きいことと同値。 -/
theorem compareBits_lt_iff_swap_gt (xs ys : List Bool) :
    compareBits xs ys = .lt ↔ compareBits ys xs = .gt := by
  constructor
  · intro h
    exact (compareBits_gt_iff ys xs).2 ((compareBits_lt_iff xs ys).1 h)
  · intro h
    exact (compareBits_lt_iff xs ys).2 ((compareBits_gt_iff ys xs).1 h)

/-- 二つの二進列が等値なら、比較順序を逆にしても等しい。 -/
theorem compareBits_eq_iff_swap (xs ys : List Bool) :
    compareBits xs ys = .eq ↔ compareBits ys xs = .eq := by
  constructor
  · intro h
    exact (compareBits_eq_iff ys xs).2 (((compareBits_eq_iff xs ys).1 h).symm)
  · intro h
    exact (compareBits_eq_iff xs ys).2 (((compareBits_eq_iff ys xs).1 h).symm)

end ArithLemmas.Pure.Binary
