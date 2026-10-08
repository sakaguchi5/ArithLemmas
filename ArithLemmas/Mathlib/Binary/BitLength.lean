module

public import ArithLemmas.Pure.Binary.Representation
public import ArithLemmas.Mathlib.Nat.BitLength
public import ArithLemmas.Mathlib.Finset.BinaryBridge

/-!
# Pureの二進列とMathlibの標準二進長（第4段階4E-3）

下位桁から並ぶ `bitsValue` の二進列と `Nat.bits` を接続し、
和・積・指定桁の復元と標準二進長の上界を導く。
原典：`OAI/Computability/LoopMatching/BitLength.lean` の
`length_bits_value_le`、`length_bits_value_add`、`length_bits_value_add_le`。
-/

public section

namespace ArithLemmas.Mathlib.Binary

open ArithLemmas.Pure.Defs.Binary

/-- 自然数の標準ビット列を `bitsValue` で解釈すると元の数に戻る。 -/
theorem bitsValue_natBits (n : ℕ) : bitsValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp only [Nat.zero_bits, Pure.Binary.bitsValue_nil]
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      change digit b + 2 * bitsValue n.bits = Nat.bit b n
      rw [ih, Nat.bit_val]
      cases b <;> simp [digit, Nat.add_comm]

/-- 自然数の標準ビット列表現の長さは、`Nat.size` に等しい。 -/
theorem natBits_length_eq_size (n : ℕ) : n.bits.length = n.size :=
  Nat.size_eq_bits_len n

/-- 正の自然数の標準ビット長を底２の切り捨て対数で表す。 -/
theorem natBits_length_eq_log_two (n : ℕ) (hn : 0 < n) :
    n.bits.length = Nat.log 2 n + 1 := by
  calc
    n.bits.length = n.size := Nat.size_eq_bits_len n
    _ = Nat.log 2 n + 1 := ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one n hn

/-- `Nat.bits` の各桁と、除算・剰余により読み出した桁は一致する。 -/
theorem natBits_digit_at (n i : ℕ) :
    (n / 2 ^ i) % 2 = digit (n.bits.getD i false) := by
  calc
    (n / 2 ^ i) % 2 = (bitsValue n.bits / 2 ^ i) % 2 := by
      rw [bitsValue_natBits]
    _ = digit (n.bits.getD i false) :=
      ArithLemmas.Mathlib.Finset.bitsValue_digit_at n.bits i

/-- 冗長な先行ゼロを含むビット列でも、標準二進長は元の列長以下。 -/
theorem value_size_le_length (xs : List Bool) :
    (bitsValue xs).size ≤ xs.length :=
  Nat.size_le.mpr (ArithLemmas.Pure.Binary.bitsValue_lt_two_pow_length xs)

/-- 原典の `length_bits_value_le` に対応する、標準ビット列の長さの上界。 -/
theorem length_bits_value_le (xs : List Bool) :
    (bitsValue xs).bits.length ≤ xs.length := by
  calc
    (bitsValue xs).bits.length = (bitsValue xs).size := Nat.size_eq_bits_len _
    _ ≤ xs.length := value_size_le_length xs

/-- 正の二進列表現の底２対数は、元の列の桁数より小さい。 -/
theorem value_log_two_lt_length (xs : List Bool) (hx : bitsValue xs ≠ 0) :
    Nat.log 2 (bitsValue xs) < xs.length :=
  Nat.log_lt_of_lt_pow hx
    (ArithLemmas.Pure.Binary.bitsValue_lt_two_pow_length xs)

/-- ビット列表現の切り上げ底２対数は、元の列の長さ以下。 -/
theorem value_clog_two_le_length (xs : List Bool) :
    Nat.clog 2 (bitsValue xs) ≤ xs.length :=
  Nat.clog_le_of_le_pow
    (ArithLemmas.Pure.Binary.bitsValue_lt_two_pow_length xs).le

/-- 二つのビット列の値の和を標準化すると、長さは最大長＋１以下。 -/
theorem length_bits_value_add (xs ys : List Bool) :
    (bitsValue xs + bitsValue ys).bits.length ≤ max xs.length ys.length + 1 := by
  calc
    (bitsValue xs + bitsValue ys).bits.length =
        (bitsValue xs + bitsValue ys).size := Nat.size_eq_bits_len _
    _ ≤ max (bitsValue xs).size (bitsValue ys).size + 1 :=
      ArithLemmas.Mathlib.Nat.size_add_le_max_add_one _ _
    _ ≤ max xs.length ys.length + 1 := by
      have hx := value_size_le_length xs
      have hy := value_size_le_length ys
      omega

/-- 入力長の上界がそれぞれ与えられた場合の加算結果の長さの上界。 -/
theorem length_bits_value_add_le (xs ys : List Bool) (a b : ℕ)
    (hx : xs.length ≤ a) (hy : ys.length ≤ b) :
    (bitsValue xs + bitsValue ys).bits.length ≤ max a b + 1 := by
  exact (length_bits_value_add xs ys).trans (by omega)

/-- 乗算した二進値を標準化したときの長さは、入力長の和以下。 -/
theorem length_bits_value_mul (xs ys : List Bool) :
    (bitsValue xs * bitsValue ys).bits.length ≤ xs.length + ys.length := by
  calc
    (bitsValue xs * bitsValue ys).bits.length =
        (bitsValue xs * bitsValue ys).size := Nat.size_eq_bits_len _
    _ ≤ (bitsValue xs).size + (bitsValue ys).size :=
      ArithLemmas.Mathlib.Nat.size_mul_le_add _ _
    _ ≤ xs.length + ys.length :=
      Nat.add_le_add (value_size_le_length xs) (value_size_le_length ys)

/-- 標準ビット列に対する乗算結果の長さの上界。 -/
theorem natBits_mul_length_le (a b : ℕ) :
    (a * b).bits.length ≤ a.bits.length + b.bits.length := by
  calc
    (a * b).bits.length = (a * b).size := Nat.size_eq_bits_len _
    _ ≤ a.size + b.size := ArithLemmas.Mathlib.Nat.size_mul_le_add a b
    _ = a.bits.length + b.bits.length := by rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]

end ArithLemmas.Mathlib.Binary
