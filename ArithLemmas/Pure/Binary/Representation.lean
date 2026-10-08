module

public import ArithLemmas.Pure.Defs.Binary.Representation

/-!
# 二進表現の導出定理

Lean 本体の自然数、`List Bool`、`omega` だけを用いる。
原典：`OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`。
-/

public section

namespace ArithLemmas.Pure.Binary

open ArithLemmas.Pure.Defs.Binary

/-- 偽のビットは０を表す。 -/
@[simp] theorem digit_false : digit false = 0 := rfl

/-- 真のビットは１を表す。 -/
@[simp] theorem digit_true : digit true = 1 := rfl

/-- どのビットの値も１以下である。 -/
theorem digit_le_one (b : Bool) : digit b ≤ 1 := by
  cases b <;> decide

/-- 空のビット列は０を表す。 -/
@[simp] theorem bitsValue_nil : bitsValue [] = 0 := rfl

/-- 先頭ビットを追加したときの値の再帰式。 -/
theorem bitsValue_cons (b : Bool) (bs : List Bool) :
    bitsValue (b :: bs) = digit b + 2 * bitsValue bs := rfl

/-- 下位桁として０を付けると、値は２倍される。 -/
theorem bitsValue_cons_false (bs : List Bool) :
    bitsValue (false :: bs) = 2 * bitsValue bs := by
  simp [bitsValue, digit]

/-- 下位桁として１を付けると、値は２倍して１を足したものになる。 -/
theorem bitsValue_cons_true (bs : List Bool) :
    bitsValue (true :: bs) = 1 + 2 * bitsValue bs := rfl

/-- 二進列の値は、桁数から定まる２の冪より真に小さい。 -/
theorem bitsValue_lt_two_pow_length (xs : List Bool) :
    bitsValue xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
      have hb := digit_le_one b
      simp only [bitsValue, List.length_cons, Nat.pow_succ]
      omega

/-- 二進列の値を、その桁数の２の冪で上から抑える。 -/
theorem bitsValue_le_two_pow_length (xs : List Bool) :
    bitsValue xs ≤ 2 ^ xs.length :=
  Nat.le_of_lt (bitsValue_lt_two_pow_length xs)

end ArithLemmas.Pure.Binary
