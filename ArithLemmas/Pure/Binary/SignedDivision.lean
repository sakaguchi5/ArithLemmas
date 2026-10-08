module

public import ArithLemmas.Pure.Binary.Division
public import ArithLemmas.Pure.Defs.Binary.SignedDivision

/-!
# 符号付き二進除算の導出定理（第2段階2D）

2B の減算、2C の自然数二進長除算の正当性を再利用する。
除数を正とし、符号付き被除数を `Int.negSucc` の規約で扱う。
商・余りの復元、余りの範囲、Lean 整数除算との一致、出力長を証明する。
原典：OpenAI `OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`。
-/

public section

namespace ArithLemmas.Pure.Binary

open ArithLemmas.Pure.Defs.Binary

/-- 非負の符号付き二進列は、二進列を自然数とみなして整数に埋め込んだ値である。 -/
@[simp] theorem signedBitsValue_false (xs : List Bool) :
    signedBitsValue false xs = (bitsValue xs : Int) := rfl

/-- 負の符号付き二進列は `-(bitsValue xs + 1)` を表す。 -/
theorem signedBitsValue_true (xs : List Bool) :
    signedBitsValue true xs = -((bitsValue xs : Int) + 1) := by
  simp [signedBitsValue, Int.negSucc_eq]

/-- 正の入力に対して、符号付き除算は 2C の自然数除算と同じ列を返す。 -/
@[simp] theorem divideSignedBits_false (divisor xs : List Bool) :
    divideSignedBits false divisor xs = divideBits divisor xs := rfl

/-- どの整数も、その符号と構成子に対応するペイロードから再構成できる。 -/
theorem signedPayload_recover (z : Int) :
    (if negativeOfInt z then Int.negSucc (signedPayload z)
      else Int.ofNat (signedPayload z)) = z := by
  cases z <;> rfl

/-- 正の除数に対する符号付き二進除算の正当性。
整数の被除数は除数と符号付き商の積に非負の余りを足した値に等しく、
余りは除数より小さい。 -/
theorem divideSignedBits_correct (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    signedBitsValue negative xs = (bitsValue divisor : Int) *
      signedBitsValue negative (divideSignedBits negative divisor xs).1 +
        (bitsValue (divideSignedBits negative divisor xs).2 : Int) ∧
    bitsValue (divideSignedBits negative divisor xs).2 < bitsValue divisor := by
  have hu := divideBits_correct divisor xs hd
  have hc : (bitsValue xs : Int) = (bitsValue divisor : Int) *
      (bitsValue (divideBits divisor xs).1 : Int) +
        (bitsValue (divideBits divisor xs).2 : Int) := by
    exact_mod_cast hu.1
  cases negative
  · simpa [divideSignedBits, signedBitsValue] using And.intro hc hu.2
  · have hp : bitsValue (subtractBits divisor [true] false) + 1 =
        bitsValue divisor := by
      have hh := subtractBits_correct divisor [true] false
        (by simp [bitsValue, digit]; omega)
      simpa [bitsValue, digit] using hh
    have hr : bitsValue (divideBits divisor xs).2 ≤
        bitsValue (subtractBits divisor [true] false) := by
      omega
    have hs : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) + bitsValue (divideBits divisor xs).2 =
          bitsValue (subtractBits divisor [true] false) := by
      simpa only [digit_false, Nat.add_zero] using
        subtractBits_correct (subtractBits divisor [true] false)
          (divideBits divisor xs).2 false
          (by simpa only [digit_false, Nat.add_zero] using hr)
    have hsn : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) + bitsValue (divideBits divisor xs).2 + 1 =
          bitsValue divisor := by omega
    have hsi : (bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) : Int) +
          (bitsValue (divideBits divisor xs).2 : Int) + 1 =
          (bitsValue divisor : Int) := by
      exact_mod_cast hsn
    have he : -((bitsValue xs : Int) + 1) = (bitsValue divisor : Int) *
        (-((bitsValue (divideBits divisor xs).1 : Int) + 1)) +
          (bitsValue (subtractBits (subtractBits divisor [true] false)
            (divideBits divisor xs).2 false) : Int) := by
      rw [hc]
      simp only [Int.mul_neg, Int.mul_add, Int.mul_one]
      omega
    have hl : bitsValue (subtractBits (subtractBits divisor [true] false)
        (divideBits divisor xs).2 false) < bitsValue divisor := by omega
    simpa [divideSignedBits, signedBitsValue, Int.negSucc_eq] using
      And.intro he hl

/-- 符号付き除算の商・余りは、元の整数を正確に復元する。 -/
theorem divideSignedBits_recover (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    signedBitsValue negative xs = (bitsValue divisor : Int) *
      signedBitsValue negative (divideSignedBits negative divisor xs).1 +
        (bitsValue (divideSignedBits negative divisor xs).2 : Int) :=
  (divideSignedBits_correct negative divisor xs hd).1

/-- 符号付き除算の余りは正の除数未満である。 -/
theorem divideSignedBits_remainder_lt (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    bitsValue (divideSignedBits negative divisor xs).2 < bitsValue divisor :=
  (divideSignedBits_correct negative divisor xs hd).2

/-- 符号付き二進除算の商はLean本体の切り下げ整数除算と一致する。 -/
theorem divideSignedBits_quotient (negative : Bool) (divisor xs : List Bool)
    (hd : 0 < bitsValue divisor) :
    signedBitsValue negative (divideSignedBits negative divisor xs).1 =
      signedBitsValue negative xs / (bitsValue divisor : Int) := by
  have h := divideSignedBits_correct negative divisor xs hd
  have hp : (0 : Int) < bitsValue divisor := by exact_mod_cast hd
  have hr : (bitsValue (divideSignedBits negative divisor xs).2 : Int) <
      (bitsValue divisor : Int) := by exact_mod_cast h.2
  have hz : (0 : Int) ≤ bitsValue (divideSignedBits negative divisor xs).2 :=
    Int.natCast_nonneg _
  have heq := h.1
  rw [Int.mul_comm (bitsValue divisor : Int)
    (signedBitsValue negative (divideSignedBits negative divisor xs).1)] at heq
  symm
  apply (Int.ediv_eq_iff_of_pos hp).mpr
  constructor <;> omega

/-- ビット列が整数のペイロードを表すなら、符号付きの値は元の整数になる。 -/
theorem signedBitsValue_negativeOfInt_payload (z : Int) (xs : List Bool)
    (h : bitsValue xs = signedPayload z) :
    signedBitsValue (negativeOfInt z) xs = z := by
  cases z with
  | ofNat n =>
      simpa [signedBitsValue, negativeOfInt, signedPayload] using
        congrArg Int.ofNat h
  | negSucc n =>
      simpa [signedBitsValue, negativeOfInt, signedPayload] using
        congrArg Int.negSucc h

/-- 符号・ペイロードと自然数除数を二進列で表したとき、整数の商が正しく得られる。
エンコード方式に依存せず、ビット列が所定の値を表すという仮定だけを使う。 -/
theorem divideSignedBits_payload_quotient (z : Int) (d : Nat) (hd : 0 < d)
    (divisor xs : List Bool) (hdiv : bitsValue divisor = d)
    (hnum : bitsValue xs = signedPayload z) :
    signedBitsValue (negativeOfInt z)
      (divideSignedBits (negativeOfInt z) divisor xs).1 = z / (d : Int) := by
  have hpositive : 0 < bitsValue divisor := by omega
  have h := divideSignedBits_quotient (negativeOfInt z) divisor xs hpositive
  rw [signedBitsValue_negativeOfInt_payload z xs hnum, hdiv] at h
  exact h

/-- 符号付き除算でも商のビット数は被除数のビット数に等しい。 -/
theorem divideSignedBits_quotient_length (negative : Bool) (divisor xs : List Bool) :
    (divideSignedBits negative divisor xs).1.length = xs.length := by
  cases negative <;>
    simpa [divideSignedBits] using divideBits_quotient_length divisor xs

/-- 符号付き除算の商と余りのビット数の総和には線形上界がある。 -/
theorem divideSignedBits_output_length_le (negative : Bool) (divisor xs : List Bool) :
    (divideSignedBits negative divisor xs).1.length +
      (divideSignedBits negative divisor xs).2.length ≤
        2 * xs.length + divisor.length + 1 := by
  have hq := divideBits_quotient_length divisor xs
  have hr := divideBits_remainder_length divisor xs
  cases negative
  · simp only [divideSignedBits, Bool.false_eq_true, ↓reduceIte]
    have h := divideBits_output_length_le divisor xs
    omega
  · simp only [divideSignedBits, ↓reduceIte, subtractBits_length, List.length_cons,
      List.length_nil, hq]
    omega

end ArithLemmas.Pure.Binary
