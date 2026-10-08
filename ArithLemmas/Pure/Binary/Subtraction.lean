module

public import ArithLemmas.Pure.Binary.Representation
public import ArithLemmas.Pure.Defs.Binary.Subtraction

/-!
# 二進減算と借りの導出定理（第2段階2B）

一桁の算術恒等式を出発点に、下位桁から繰り返す減算の正当性を証明する。
Lean本体の `omega` を利用し、Mathlibには依存しない。
原典：OpenAI `OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`。
-/

public section

namespace ArithLemmas.Pure.Binary

open ArithLemmas.Pure.Defs.Binary

/-- 一桁の差と借りは、二進数の減算の桁ごとの恒等式を満たす。 -/
theorem subtraction_column (a b c : Bool) :
    digit a + 2 * digit (nextBorrow a b c) =
      digit (differenceDigit a b c) + digit b + digit c := by
  cases a <;> cases b <;> cases c <;> decide

/-- 全体で減算できるなら、次の桁でも借りを含めて減算できる。 -/
private theorem tail_borrow_le (a b c : Bool) (x y : Nat)
    (h : digit b + 2 * y + digit c ≤ digit a + 2 * x) :
    y + digit (nextBorrow a b c) ≤ x := by
  have he := subtraction_column a b c
  have ho := digit_le_one (differenceDigit a b c)
  omega

/-- 下位桁の恒等式と上位桁の等式を結合する。 -/
private theorem subtraction_lift (a b c : Bool) (x y r : Nat)
    (hr : r + y + digit (nextBorrow a b c) = x) :
    (digit (differenceDigit a b c) + 2 * r) +
      (digit b + 2 * y) + digit c = digit a + 2 * x := by
  have he := subtraction_column a b c
  omega

/-- 被減数が減数と初期借りの和以上なら、二進減算は元の値を復元する。
`bitsValue (subtractBits xs ys c) + bitsValue ys + digit c = bitsValue xs`。 -/
theorem subtractBits_correct (xs ys : List Bool) (c : Bool)
    (h : bitsValue ys + digit c ≤ bitsValue xs) :
    bitsValue (subtractBits xs ys c) + bitsValue ys + digit c = bitsValue xs := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil =>
      simp only [bitsValue, Nat.zero_add] at h
      simpa [subtractBits, bitsValue] using Nat.eq_zero_of_le_zero h
    | cons b bs ih =>
      have ht := tail_borrow_le false b c 0 (bitsValue bs)
        (by simpa [bitsValue, digit] using h)
      have hr := ih (nextBorrow false b c) (by simpa [bitsValue] using ht)
      have hh := subtraction_lift false b c 0 (bitsValue bs)
        (bitsValue (subtractBits [] bs (nextBorrow false b c)))
        (by simpa [bitsValue] using hr)
      simpa [subtractBits, bitsValue, digit] using hh
  | cons a as ih =>
    cases ys with
    | nil =>
      have ht := tail_borrow_le a false c (bitsValue as) 0
        (by simpa [bitsValue, digit] using h)
      have hr := ih [] (nextBorrow a false c) (by simpa [bitsValue] using ht)
      have hh := subtraction_lift a false c (bitsValue as) 0
        (bitsValue (subtractBits as [] (nextBorrow a false c)))
        (by simpa [bitsValue] using hr)
      simpa [subtractBits, bitsValue, digit] using hh
    | cons b bs =>
      have ht := tail_borrow_le a b c (bitsValue as) (bitsValue bs)
        (by simpa [bitsValue, digit] using h)
      have hr := ih bs (nextBorrow a b c) ht
      simpa only [subtractBits, bitsValue] using
        subtraction_lift a b c (bitsValue as) (bitsValue bs)
          (bitsValue (subtractBits as bs (nextBorrow a b c))) hr

/-- 二進減算が返すビット列の長さは、二つの入力の長さの最大値と等しい。 -/
theorem subtractBits_length (xs ys : List Bool) (c : Bool) :
    (subtractBits xs ys c).length = max xs.length ys.length := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => simp [subtractBits]
    | cons b bs ih => simp [subtractBits, ih]
  | cons a as ih =>
    cases ys with
    | nil => simp [subtractBits, ih]
    | cons b bs =>
      simp only [subtractBits, List.length_cons, ih]
      omega

/-- 初期借りを含め、減算結果の数値は自然数の差と一致する。 -/
theorem subtractBits_value (xs ys : List Bool) (c : Bool)
    (h : bitsValue ys + digit c ≤ bitsValue xs) :
    bitsValue (subtractBits xs ys c) = bitsValue xs - (bitsValue ys + digit c) := by
  have hr := subtractBits_correct xs ys c h
  omega

/-- 初期借りがない場合、二進減算は自然数の通常の減算と一致する。 -/
theorem subtractBits_value_no_borrow (xs ys : List Bool)
    (h : bitsValue ys ≤ bitsValue xs) :
    bitsValue (subtractBits xs ys false) = bitsValue xs - bitsValue ys := by
  have h' : bitsValue ys + digit false ≤ bitsValue xs := by
    simpa [digit] using h
  simpa [digit] using subtractBits_value xs ys false h'

/-- 被減数が減数以上なら、初期借りなしの減算は復元恒等式を満たす。 -/
theorem subtractBits_add (xs ys : List Bool) (h : bitsValue ys ≤ bitsValue xs) :
    bitsValue (subtractBits xs ys false) + bitsValue ys = bitsValue xs := by
  have h' : bitsValue ys + digit false ≤ bitsValue xs := by
    simpa [digit] using h
  simpa [digit] using subtractBits_correct xs ys false h'

end ArithLemmas.Pure.Binary
