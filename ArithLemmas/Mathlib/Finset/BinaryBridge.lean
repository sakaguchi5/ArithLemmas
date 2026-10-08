module

public import ArithLemmas.Pure.Binary.Representation
public import ArithLemmas.Mathlib.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# 二進表現と有限和のBridge（第3段階3A）

Pure の `bitsValue` と既存の Mathlib 層の `baseValue` が表す値の一致を証明する。
二進列は下位桁から並ぶ `List Bool` であり、範囲外の桁は `false` として読む。
Pure → Mathlib という依存方向は作らず、Mathlib 側から Pure の定理を使う。
出典：OpenAI の二進算術と ArithLemmas の `baseValue` を接続する派生定理。
-/

public section

namespace ArithLemmas.Mathlib.Finset

open ArithLemmas.Pure.Defs.Binary
open ArithLemmas.Pure.Binary

/-- 二進列の値は、基数２・桁数 `xs.length` の有限和値 `baseValue` に一致する。 -/
theorem bitsValue_eq_baseValue (xs : List Bool) :
    bitsValue xs = baseValue 2 xs.length (fun i => digit (xs.getD i false)) := by
  induction xs with
  | nil =>
      simp [bitsValue, baseValue]
  | cons b bs ih =>
      change digit b + 2 * bitsValue bs =
        baseValue 2 (bs.length + 1) (fun i => digit ((b :: bs).getD i false))
      rw [baseValue_succ]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      exact congrArg (fun n : Nat => digit b + 2 * n) ih

/-- `bitsValue` と、各桁を２の冪で重み付けした `Finset.range` の和は等しい。 -/
theorem bitsValue_eq_finset_sum (xs : List Bool) :
    bitsValue xs =
      ∑ i ∈ Finset.range xs.length, digit (xs.getD i false) * 2 ^ i := by
  simpa only [baseValue] using bitsValue_eq_baseValue xs

/-- 有限和の先頭桁を取り出すと、残りは２倍した有限和になる。 -/
theorem baseValue_two_cons (b : Bool) (bs : List Bool) :
    baseValue 2 (b :: bs).length (fun i => digit ((b :: bs).getD i false)) =
      digit b + 2 * baseValue 2 bs.length (fun i => digit (bs.getD i false)) := by
  simp only [List.length_cons]
  rw [baseValue_succ]
  simp only [List.getD_cons_zero, List.getD_cons_succ]

/-- 下位一桁は、有限和の２による剰余として復元できる。 -/
theorem bitsValue_cons_mod_two (b : Bool) (bs : List Bool) :
    bitsValue (b :: bs) % 2 = digit b := by
  rw [bitsValue_eq_baseValue]
  have hm := baseValue_mod 2 (b :: bs).length
    (fun i => digit ((b :: bs).getD i false)) (Nat.zero_lt_succ _)
  rw [hm]
  simp only [List.getD_cons_zero]
  cases b <;> decide

/-- 二進列の値を２で割ると、下位一桁を除いた残りの値になる。 -/
theorem bitsValue_cons_div_two (b : Bool) (bs : List Bool) :
    bitsValue (b :: bs) / 2 = bitsValue bs := by
  cases b <;> simp [bitsValue, digit]
  omega

/-- `i` 桁右へずらした後の剰余で、元の列の `i` 番目のビットを復元する。
    範囲外の桁は０を返す。 -/
theorem bitsValue_digit_at (xs : List Bool) (i : Nat) :
    (bitsValue xs / 2 ^ i) % 2 = digit (xs.getD i false) := by
  induction xs generalizing i with
  | nil =>
      simp [bitsValue, List.getD, digit]
  | cons b bs ih =>
      cases i with
      | zero =>
          simp only [pow_zero, Nat.div_one, List.getD_cons_zero]
          exact bitsValue_cons_mod_two b bs
      | succ i =>
          simp only [List.getD_cons_succ]
          calc
            (bitsValue (b :: bs) / 2 ^ (i + 1)) % 2 =
                ((bitsValue (b :: bs) / 2) / 2 ^ i) % 2 := by
                  rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm (2 ^ i) 2]
            _ = (bitsValue bs / 2 ^ i) % 2 := by rw [bitsValue_cons_div_two]
            _ = digit (bs.getD i false) := ih i

/-- 基数２の有限和表現から、任意の指定桁を復元する。 -/
theorem baseValue_two_digit_at (xs : List Bool) (i : Nat) :
    (baseValue 2 xs.length (fun j => digit (xs.getD j false)) / 2 ^ i) % 2 =
      digit (xs.getD i false) := by
  rw [← bitsValue_eq_baseValue xs]
  exact bitsValue_digit_at xs i

/-- 二進列の連結は、後半の値を前半の桁数だけ２倍冪シフトして加えた値になる。 -/
theorem bitsValue_append (xs ys : List Bool) :
    bitsValue (xs ++ ys) = bitsValue xs + 2 ^ xs.length * bitsValue ys := by
  induction xs with
  | nil => simp [bitsValue]
  | cons b bs ih =>
      simp only [List.cons_append, bitsValue_cons, List.length_cons, pow_succ]
      rw [ih]
      ring

/-- 連結した二進列に対して、`baseValue` も同じシフト和の法則を満たす。 -/
theorem baseValue_two_append (xs ys : List Bool) :
    baseValue 2 (xs ++ ys).length (fun i => digit ((xs ++ ys).getD i false)) =
      baseValue 2 xs.length (fun i => digit (xs.getD i false)) +
        2 ^ xs.length * baseValue 2 ys.length (fun i => digit (ys.getD i false)) := by
  calc
    _ = bitsValue (xs ++ ys) := (bitsValue_eq_baseValue (xs ++ ys)).symm
    _ = bitsValue xs + 2 ^ xs.length * bitsValue ys := bitsValue_append xs ys
    _ = _ := by rw [bitsValue_eq_baseValue xs, bitsValue_eq_baseValue ys]

/-- 連結した二進列の有限和を、二つの有限和に分解する。 -/
theorem binary_sum_append (xs ys : List Bool) :
    (∑ i ∈ Finset.range (xs ++ ys).length,
      digit ((xs ++ ys).getD i false) * 2 ^ i) =
      (∑ i ∈ Finset.range xs.length, digit (xs.getD i false) * 2 ^ i) +
        2 ^ xs.length *
          (∑ i ∈ Finset.range ys.length, digit (ys.getD i false) * 2 ^ i) := by
  calc
    _ = bitsValue (xs ++ ys) := (bitsValue_eq_finset_sum (xs ++ ys)).symm
    _ = bitsValue xs + 2 ^ xs.length * bitsValue ys := bitsValue_append xs ys
    _ = _ := by rw [bitsValue_eq_finset_sum xs, bitsValue_eq_finset_sum ys]

/-- 二進列の有限和も、その桁数に応じた２の冪未満となる。 -/
theorem binary_sum_lt_two_pow_length (xs : List Bool) :
    (∑ i ∈ Finset.range xs.length, digit (xs.getD i false) * 2 ^ i) <
      2 ^ xs.length := by
  rw [← bitsValue_eq_finset_sum xs]
  exact bitsValue_lt_two_pow_length xs

end ArithLemmas.Mathlib.Finset
