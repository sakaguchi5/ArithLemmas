module

public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity
/-!
# 二進長と自然数の対数（第4段階4E-3）

標準の `Nat.size`・`Nat.log`・`Nat.clog` を再定義せず、長さと冪の
間を往復する汎用補題をまとめる。
原典：`OAI/Computability/LoopMatching/BitLength.lean`、
`OAI/Combinatorics/ContingencyTables/Dense/DenseWordProgram.lean`。
-/

public section

namespace ArithLemmas.Mathlib.Nat

/-- 自然数は、その標準二進長の２の冪より真に小さい。 -/
theorem lt_two_pow_size (n : ℕ) : n < 2 ^ n.size :=
  Nat.lt_size_self n

/-- ２の冪未満という評価から、二進長の上界を得る。 -/
theorem size_le_of_lt_two_pow (n k : ℕ) (h : n < 2 ^ k) : n.size ≤ k :=
  Nat.size_le.mpr h

/-- 指定桁数が標準二進長に達していなければ、対応する２の冪以上である。 -/
theorem two_pow_le_of_lt_size (n k : ℕ) (h : k < n.size) : 2 ^ k ≤ n :=
  Nat.lt_size.mp h

/-- 正の自然数の二進長は、底２の切り捨て対数に１を加えた長さに等しい。 -/
theorem size_eq_log_two_add_one (n : ℕ) (hn : 0 < n) :
    n.size = Nat.log 2 n + 1 := by
  have hlo : 2 ^ (Nat.log 2 n) ≤ n :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  have hhi : n < 2 ^ (Nat.log 2 n + 1) :=
    Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n
  exact le_antisymm (Nat.size_le.mpr hhi)
    (Nat.succ_le_of_lt (Nat.lt_size.mpr hlo))

/-- `Nat.log2` を使っても標準二進長の表示は同じである。 -/
theorem size_eq_log2_add_one (n : ℕ) (hn : 0 < n) :
    n.size = Nat.log2 n + 1 := by
  rw [Nat.log2_eq_log_two]
  exact size_eq_log_two_add_one n hn

/-- ２の冪そのものの二進長は指数より１大きい。 -/
theorem size_two_pow (k : ℕ) : (2 ^ k).size = k + 1 :=
  Nat.size_pow

/-- 自然数の切り上げ底２対数は、１を引いた数の標準二進長に等しい。 -/
theorem clog_two_eq_size_pred (n : ℕ) :
    Nat.clog 2 n = (n - 1).size := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ)), Nat.size_le]
  have hp : 0 < (2 : ℕ) ^ k := by positivity
  omega

/-- 切り上げ底２対数は、元の数の標準二進長以下である。 -/
theorem clog_two_le_size (n : ℕ) : Nat.clog 2 n ≤ n.size :=
  (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
    (Nat.lt_size_self n).le

/-- 二つの自然数の和の二進長は、大きい方の長さに１を加えた値以下。 -/
theorem size_add_le_max_add_one (a b : ℕ) :
    (a + b).size ≤ max a.size b.size + 1 := by
  apply Nat.size_le.mpr
  have ha : a < 2 ^ (max a.size b.size) :=
    (Nat.lt_size_self a).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hb : b < 2 ^ (max a.size b.size) :=
    (Nat.lt_size_self b).trans_le
      (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  rw [pow_succ]
  omega

/-- 自然数の積の二進長は、二つの二進長の和以下。 -/
theorem size_mul_le_add (a b : ℕ) :
    (a * b).size ≤ a.size + b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  calc
    a * b ≤ (2 ^ a.size) * b :=
      Nat.mul_le_mul_right b (Nat.lt_size_self a).le
    _ < (2 ^ a.size) * (2 ^ b.size) :=
      Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self b)
        (pow_pos (by decide : 0 < (2 : ℕ)) _)

/-- 底２の対数が与える整数の下界。ゼロ以外で成り立つ。 -/
theorem two_pow_log_le (n : ℕ) (hn : n ≠ 0) :
    2 ^ Nat.log 2 n ≤ n :=
  Nat.pow_log_le_self 2 hn

/-- 底２の対数が与える整数の真の上界。ゼロでも成り立つ。 -/
theorem lt_two_pow_log_succ (n : ℕ) :
    n < 2 ^ (Nat.log 2 n + 1) :=
  Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) n

/-- 底２の切り上げ対数が与える冪上界。 -/
theorem le_two_pow_clog (n : ℕ) :
    n ≤ 2 ^ Nat.clog 2 n :=
  Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) n

end ArithLemmas.Mathlib.Nat
