module

public import ArithLemmas.Pure.Binary.SignedDivision
public import ArithLemmas.Pure.Defs.Binary.Cost

/-!
# 二進長除算・符号付き除算の計算コスト評価（第2段階2D）

2B・2C の出力長の定理を使い、走査コストの具体的上界を証明する。
二次上界は非線形戦術を使わず、自然数の単調性と分配法則から導出する。
数学的なモデル上のビット走査数であり、実行時間の実測値ではない。
原典：OpenAI `OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`。
-/

public section

namespace ArithLemmas.Pure.Binary

open ArithLemmas.Pure.Defs.Binary

/-- 二つのビット列を比較・減算する走査コストは長い方のビット数に１を足した値。 -/
theorem bitScanCost_eq (xs ys : List Bool) :
    bitScanCost xs ys = max xs.length ys.length + 1 := by
  induction xs generalizing ys with
  | nil =>
      induction ys with
      | nil => simp [bitScanCost]
      | cons b bs ih => simp [bitScanCost, ih]
  | cons a as ih =>
      cases ys with
      | nil => simp [bitScanCost, ih]
      | cons b bs =>
          simp only [bitScanCost, List.length_cons, ih]
          omega

/-- 二進除算の反復回数は被除数のビット数と一致する。 -/
theorem divisionIterations_eq_length (xs : List Bool) :
    divisionIterations xs = xs.length := by
  induction xs <;> simp_all [divisionIterations]

/-- 自然数二進除算のコスト上界の反復ステップで使う積の恒等式。 -/
private theorem division_bound_step (n d : Nat) :
    (n + 1) * (n + 1 + 4 * d + 4) + 1 =
      n * (n + 4 * d + 4) + 1 + (2 * n + 4 * d + 5) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  omega

/-- 二進長除算のビット走査コストは、被除数と除数のビット数で評価できる。 -/
theorem divisionBitCost_le (divisor xs : List Bool) :
    divisionBitCost divisor xs ≤
      xs.length * (xs.length + 4 * divisor.length + 4) + 1 := by
  induction xs with
  | nil => simp [divisionBitCost]
  | cons b bs ih =>
      have hr := divideBits_remainder_length divisor bs
      have hs : bitScanCost (b :: (divideBits divisor bs).2) divisor ≤
          bs.length + 2 * divisor.length + 2 := by
        rw [bitScanCost_eq]
        simp only [List.length_cons]
        omega
      simp only [divisionBitCost, List.length_cons]
      rw [division_bound_step bs.length divisor.length]
      split <;> omega

/-- 符号付き除算で追加する最初の余り補正の走査回数の上界。 -/
theorem signedCorrection_first_le (divisor : List Bool) :
    bitScanCost divisor [true] ≤ divisor.length + 2 := by
  rw [bitScanCost_eq]
  simp only [List.length_cons, List.length_nil]
  omega

/-- 符号付き除算で追加する二番目の余り補正の走査回数の上界。 -/
theorem signedCorrection_second_le (divisor xs : List Bool) :
    bitScanCost (subtractBits divisor [true] false) (divideBits divisor xs).2 ≤
      xs.length + 2 * divisor.length + 2 := by
  have hr := divideBits_remainder_length divisor xs
  rw [bitScanCost_eq, subtractBits_length]
  simp only [List.length_cons, List.length_nil]
  omega

/-- 符号付き二進除算の走査コストの具体的上界。 -/
theorem signedDivisionBitCost_le (negative : Bool) (divisor xs : List Bool) :
    signedDivisionBitCost negative divisor xs ≤
      xs.length * (xs.length + 4 * divisor.length + 4) +
        xs.length + 3 * divisor.length + 5 := by
  have hu := divisionBitCost_le divisor xs
  have hs₁ := signedCorrection_first_le divisor
  have hs₂ := signedCorrection_second_le divisor xs
  cases negative <;>
    simp only [signedDivisionBitCost, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- `n` ビットと `d` ビットの具体的コスト上界は、総入力長の二乗で抑えられる。 -/
private theorem quadratic_majorant (n d : Nat) :
    n * (n + 4 * d + 4) + n + 3 * d + 5 ≤
      6 * (n + d + 1) ^ 2 := by
  let s := n + d + 1
  have hf : n + 4 * d + 4 ≤ 4 * s := by
    dsimp [s]
    omega
  have hfirst : n * (n + 4 * d + 4) ≤ (4 * n) * s := by
    calc
      _ ≤ n * (4 * s) := Nat.mul_le_mul_left n hf
      _ = (4 * n) * s := by
        rw [← Nat.mul_assoc, Nat.mul_comm n 4]
  have hrest : n + 3 * d + 5 ≤ 5 * s := by
    dsimp [s]
    omega
  calc
    _ ≤ (4 * n + 5) * s := by
      rw [Nat.add_mul]
      omega
    _ ≤ (6 * s) * s :=
      Nat.mul_le_mul_right s (by dsimp [s]; omega)
    _ = 6 * (n + d + 1) ^ 2 := by
      dsimp [s]
      simp [Nat.pow_two, Nat.mul_assoc]

/-- 自然数二進除算のビット走査コストは総入力長について二次以下である。 -/
theorem divisionBitCost_quadratic (divisor xs : List Bool) :
    divisionBitCost divisor xs ≤
      6 * (xs.length + divisor.length + 1) ^ 2 := by
  have h := divisionBitCost_le divisor xs
  have hquad := quadratic_majorant xs.length divisor.length
  omega

/-- 符号付き二進除算のビット走査コストも総入力長について二次以下である。 -/
theorem signedDivisionBitCost_quadratic (negative : Bool) (divisor xs : List Bool) :
    signedDivisionBitCost negative divisor xs ≤
      6 * (xs.length + divisor.length + 1) ^ 2 := by
  have h₁ := signedDivisionBitCost_le negative divisor xs
  have h₂ := quadratic_majorant xs.length divisor.length
  omega

end ArithLemmas.Pure.Binary
