module

public import ArithLemmas.Pure.Binary.Cost
public import ArithLemmas.Mathlib.Binary.BitLength

/-!
# 二進除算の計算コストと対数評価（第4段階4E-3）

Pure層にある二次コスト評価を再利用し、標準二進長で表示する。
先行ゼロが含まれる任意のリストの長さを値の対数に置き換えることは
できないため、値と同じ最小桁数で表すという仮定を明示する。
-/

public section

namespace ArithLemmas.Mathlib.Binary

open ArithLemmas.Pure.Defs.Binary

/-- 最小桁数で表した被除数と除数の反復回数は、被除数の標準二進長。 -/
theorem divisionIterations_eq_value_size (xs : List Bool)
    (hx : xs.length = (bitsValue xs).size) :
    divisionIterations xs = (bitsValue xs).size := by
  rw [ArithLemmas.Pure.Binary.divisionIterations_eq_length, hx]

/-- 正規化された二進入力の自然数除算コストは、値の二進長について二次以下。 -/
theorem divisionBitCost_le_value_sizes (divisor xs : List Bool)
    (hx : xs.length = (bitsValue xs).size)
    (hd : divisor.length = (bitsValue divisor).size) :
    divisionBitCost divisor xs ≤
      6 * ((bitsValue xs).size + (bitsValue divisor).size + 1) ^ 2 := by
  simpa only [hx, hd] using
    ArithLemmas.Pure.Binary.divisionBitCost_quadratic divisor xs

/-- 正規化された符号付き二進入力の走査コストも、値の二進長について二次以下。 -/
theorem signedDivisionBitCost_le_value_sizes
    (negative : Bool) (divisor xs : List Bool)
    (hx : xs.length = (bitsValue xs).size)
    (hd : divisor.length = (bitsValue divisor).size) :
    signedDivisionBitCost negative divisor xs ≤
      6 * ((bitsValue xs).size + (bitsValue divisor).size + 1) ^ 2 := by
  simpa only [hx, hd] using
    ArithLemmas.Pure.Binary.signedDivisionBitCost_quadratic negative divisor xs

/-- 両入力の値が正で先行ゼロのない場合、自然数除算コストを対数で評価する。 -/
theorem divisionBitCost_le_logs (divisor xs : List Bool)
    (hxp : 0 < bitsValue xs) (hdp : 0 < bitsValue divisor)
    (hx : xs.length = (bitsValue xs).size)
    (hd : divisor.length = (bitsValue divisor).size) :
    divisionBitCost divisor xs ≤
      6 * ((Nat.log 2 (bitsValue xs) + 1) +
          (Nat.log 2 (bitsValue divisor) + 1) + 1) ^ 2 := by
  have hb := divisionBitCost_le_value_sizes divisor xs hx hd
  rw [ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one _ hxp,
    ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one _ hdp] at hb
  exact hb

/-- 両入力が正で正規化されていれば、符号付き除算コストも対数で評価できる。 -/
theorem signedDivisionBitCost_le_logs
    (negative : Bool) (divisor xs : List Bool)
    (hxp : 0 < bitsValue xs) (hdp : 0 < bitsValue divisor)
    (hx : xs.length = (bitsValue xs).size)
    (hd : divisor.length = (bitsValue divisor).size) :
    signedDivisionBitCost negative divisor xs ≤
      6 * ((Nat.log 2 (bitsValue xs) + 1) +
          (Nat.log 2 (bitsValue divisor) + 1) + 1) ^ 2 := by
  have hb := signedDivisionBitCost_le_value_sizes negative divisor xs hx hd
  rw [ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one _ hxp,
    ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one _ hdp] at hb
  exact hb


/-- 標準の `Nat.bits` を使えば、正規化の仮定なしで値の二進長から除算コストを抑えられる。 -/
theorem divisionBitCost_natBits (d n : ℕ) :
    divisionBitCost d.bits n.bits ≤ 6 * (n.size + d.size + 1) ^ 2 := by
  have hn : n.bits.length = (bitsValue n.bits).size := by
    rw [bitsValue_natBits]
    exact Nat.size_eq_bits_len n
  have hd : d.bits.length = (bitsValue d.bits).size := by
    rw [bitsValue_natBits]
    exact Nat.size_eq_bits_len d
  simpa only [bitsValue_natBits] using
    divisionBitCost_le_value_sizes d.bits n.bits hn hd

/-- `Nat.bits` による符号付き除算も、ゼロを含む入力で二進長の二乗以下。 -/
theorem signedDivisionBitCost_natBits (negative : Bool) (d n : ℕ) :
    signedDivisionBitCost negative d.bits n.bits ≤
      6 * (n.size + d.size + 1) ^ 2 := by
  have hn : n.bits.length = (bitsValue n.bits).size := by
    rw [bitsValue_natBits]
    exact Nat.size_eq_bits_len n
  have hd : d.bits.length = (bitsValue d.bits).size := by
    rw [bitsValue_natBits]
    exact Nat.size_eq_bits_len d
  simpa only [bitsValue_natBits] using
    signedDivisionBitCost_le_value_sizes negative d.bits n.bits hn hd

/-- 正の自然数を標準ビット列へ変換した場合の自然数除算の対数コスト上界。 -/
theorem divisionBitCost_natBits_log (d n : ℕ) (hn : 0 < n) (hd : 0 < d) :
    divisionBitCost d.bits n.bits ≤
      6 * ((Nat.log 2 n + 1) + (Nat.log 2 d + 1) + 1) ^ 2 := by
  have h := divisionBitCost_natBits d n
  rw [ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one n hn,
    ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one d hd] at h
  exact h

/-- 正の自然数の標準ビット列に対する符号付き二進除算の対数コスト上界。 -/
theorem signedDivisionBitCost_natBits_log
    (negative : Bool) (d n : ℕ) (hn : 0 < n) (hd : 0 < d) :
    signedDivisionBitCost negative d.bits n.bits ≤
      6 * ((Nat.log 2 n + 1) + (Nat.log 2 d + 1) + 1) ^ 2 := by
  have h := signedDivisionBitCost_natBits negative d n
  rw [ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one n hn,
    ArithLemmas.Mathlib.Nat.size_eq_log_two_add_one d hd] at h
  exact h

end ArithLemmas.Mathlib.Binary
