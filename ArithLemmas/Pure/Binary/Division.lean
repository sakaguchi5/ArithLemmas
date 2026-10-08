module

public import ArithLemmas.Pure.Binary.Comparison
public import ArithLemmas.Pure.Binary.Subtraction
public import ArithLemmas.Pure.Defs.Binary.Division

/-!
# 自然数の二進除算の導出定理（第2段階2C）

第2段階2Aの比較定理・2Bの減算定理から二進長除算の正当性を導出する。
正の除数に対し、被除数 = 除数 * 商 + 余りと、余り < 除数を証明する。
出力の長さも評価する。Mathlibには依存しない。
原典：OpenAI `OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`。
-/

public section

namespace ArithLemmas.Pure.Binary

open ArithLemmas.Pure.Defs.Binary

/-- 二進長除算の空入力では、商と余りはいずれも空列になる。 -/
@[simp] theorem divideBits_nil (divisor : List Bool) :
    divideBits divisor [] = ([], []) := rfl

/-- 除数を掛けた二倍の商は、積を二倍したものに一致する。 -/
private theorem mul_double (d q : Nat) : d * (2 * q) = 2 * (d * q) := by
  calc
    d * (2 * q) = (d * 2) * q := (Nat.mul_assoc d 2 q).symm
    _ = (2 * d) * q := by rw [Nat.mul_comm d 2]
    _ = 2 * (d * q) := Nat.mul_assoc 2 d q

/-- 一桁を付け足した商との積を展開する。 -/
private theorem mul_bit_succ (d q : Nat) :
    d * (1 + 2 * q) = d + 2 * (d * q) := by
  rw [Nat.mul_add, Nat.mul_one, mul_double]

/-- 二進長除算の正当性。正の除数について
`被除数 = 除数 * 商 + 余り` かつ `余り < 除数` が成り立つ。 -/
theorem divideBits_correct (divisor xs : List Bool) (hd : 0 < bitsValue divisor) :
    bitsValue xs = bitsValue divisor * bitsValue (divideBits divisor xs).1 +
      bitsValue (divideBits divisor xs).2 ∧
    bitsValue (divideBits divisor xs).2 < bitsValue divisor := by
  induction xs with
  | nil =>
      simpa [divideBits, bitsValue] using hd
  | cons b bs ih =>
      have hb := digit_le_one b
      by_cases hc : compareBits (b :: (divideBits divisor bs).2) divisor = .lt
      · have hl := (compareBits_lt_iff _ _).mp hc
        simp only [divideBits, hc, ↓reduceIte]
        simp only [bitsValue, digit_false, Nat.zero_add] at hl ⊢
        constructor
        · have hm := mul_double (bitsValue divisor) (bitsValue (divideBits divisor bs).1)
          omega
        · exact hl
      · have hle : bitsValue divisor ≤ bitsValue (b :: (divideBits divisor bs).2) := by
          exact Nat.le_of_not_gt (fun h => hc ((compareBits_lt_iff _ _).mpr h))
        have hs := subtractBits_correct (b :: (divideBits divisor bs).2) divisor false
          (by simpa [digit] using hle)
        simp only [digit_false, Nat.add_zero] at hs
        simp only [divideBits, hc, ↓reduceIte, bitsValue, digit_true]
        simp only [bitsValue] at hs
        constructor
        · have hm := mul_bit_succ (bitsValue divisor) (bitsValue (divideBits divisor bs).1)
          omega
        · omega

/-- 正の除数について、計算結果の商・余りは被除数を復元する。 -/
theorem divideBits_recover (divisor xs : List Bool) (hd : 0 < bitsValue divisor) :
    bitsValue xs = bitsValue divisor * bitsValue (divideBits divisor xs).1 +
      bitsValue (divideBits divisor xs).2 :=
  (divideBits_correct divisor xs hd).1

/-- 正の除数について、計算結果の余りは除数より小さい。 -/
theorem divideBits_remainder_lt (divisor xs : List Bool) (hd : 0 < bitsValue divisor) :
    bitsValue (divideBits divisor xs).2 < bitsValue divisor :=
  (divideBits_correct divisor xs hd).2

/-- 二進長除算の商のビット数は、被除数のビット数に等しい。 -/
theorem divideBits_quotient_length (divisor xs : List Bool) :
    (divideBits divisor xs).1.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
      simp only [divideBits]
      split <;> simp [ih]

/-- 二進長除算の余りのビット数は被除数と除数のビット数の和以下。 -/
theorem divideBits_remainder_length (divisor xs : List Bool) :
    (divideBits divisor xs).2.length ≤ xs.length + divisor.length := by
  induction xs with
  | nil => simp [divideBits]
  | cons b bs ih =>
      simp only [divideBits]
      split
      · simp only [List.length_cons]
        omega
      · simp only [subtractBits_length, List.length_cons]
        omega

/-- 商と余りを合わせた出力の長さには線形上界がある。 -/
theorem divideBits_output_length_le (divisor xs : List Bool) :
    (divideBits divisor xs).1.length + (divideBits divisor xs).2.length ≤
      2 * xs.length + divisor.length := by
  rw [divideBits_quotient_length]
  have h := divideBits_remainder_length divisor xs
  omega

/-- 除数が正なら、被除数は除数と商の積以上である。 -/
theorem divideBits_product_le (divisor xs : List Bool) (hd : 0 < bitsValue divisor) :
    bitsValue divisor * bitsValue (divideBits divisor xs).1 ≤ bitsValue xs := by
  have h := divideBits_recover divisor xs hd
  omega

end ArithLemmas.Pure.Binary
