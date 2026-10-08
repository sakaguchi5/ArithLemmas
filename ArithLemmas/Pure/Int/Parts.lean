module

public import ArithLemmas.Pure.Int.Basic
public import ArithLemmas.Pure.Defs.Int.Parts

/-!
# 整数の正負分解の導出定理

整数を非負の二つの自然数の差として表現する。
原典：Computability/RationalHitting/SignedArithmetic (`int_decompose`)。
-/

public section

namespace ArithLemmas.Pure.Int

open ArithLemmas.Pure.Defs.Int

/-- 非負整数の正部分はその自然数値に等しい。 -/
theorem positivePart_ofNat (n : Nat) : positivePart (Int.ofNat n) = n := rfl

/-- 非負整数の負部分はゼロである。 -/
theorem negativePart_ofNat (n : Nat) : negativePart (Int.ofNat n) = 0 := rfl

/-- 負整数 `-(n+1)` の正部分はゼロである。 -/
theorem positivePart_negSucc (n : Nat) : positivePart (Int.negSucc n) = 0 := rfl

/-- 負整数 `-(n+1)` の負部分は `n+1` である。 -/
theorem negativePart_negSucc (n : Nat) : negativePart (Int.negSucc n) = n + 1 := rfl

/-- すべての整数は、その正部分から負部分を引くことで復元される。 -/
theorem int_decompose (z : Int) :
    (positivePart z : Int) - (negativePart z : Int) = z := by
  cases z with
  | ofNat n => simp [positivePart, negativePart]
  | negSucc n => simp [positivePart, negativePart] <;> omega

/-- 正負部分の値がそれぞれ一致すれば、整数そのものも一致する。 -/
theorem int_parts_injective :
    Function.Injective (fun z : Int => (positivePart z, negativePart z)) := by
  intro a b h
  have hp := congrArg (fun z : Nat × Nat => (z.1 : Int) - (z.2 : Int)) h
  exact (int_decompose a).symm.trans (hp.trans (int_decompose b))

/-- 二つの整数の正部分・負部分が共に等しいことは整数が等しいことと同値である。 -/
theorem int_parts_eq_iff {a b : Int} :
    (positivePart a, negativePart a) =
      (positivePart b, negativePart b) ↔ a = b := by
  constructor
  · intro h
    exact int_parts_injective h
  · intro h
    exact congrArg (fun z : Int => (positivePart z, negativePart z)) h

end ArithLemmas.Pure.Int
