module

public import ArithLemmas.Pure.Defs.Nat.Basic

/-!
# 自然数の導出定理

Lean 本体の自然数、整除、最大公約数、最小公倍数だけに依存する。
既存の数学ライブラリを追加で読み込まず、定義から性質を導く。
-/

public section

namespace ArithLemmas.Pure.Nat

open ArithLemmas.Pure.Defs.Nat

/-- 反復回数０では、入力した二つの自然数をそのまま返す。-/
theorem euclidRun_zero_steps (a b : Nat) : euclidRun 0 a b = (a, b) := rfl

/-- １回以上の反復では、まず除数が０かどうかを判定する。-/
theorem euclidRun_succ (k a b : Nat) :
    euclidRun (k + 1) a b =
      if b = 0 then (a, 0) else euclidRun k b (a % b) := rfl

/-- 第２成分が０の状態は、何回反復しても変化しない。-/
theorem euclidRun_zero (k a : Nat) : euclidRun k a 0 = (a, 0) := by
  cases k <;> simp [euclidRun]

/-- 最大公約数による分解の第１成分は最大公約数である。-/
theorem gcdSplit_first (a d : Nat) : (gcdSplit a d).1 = Nat.gcd a d := rfl

/-- 最大公約数による分解の第２成分は、その最大公約数による商である。-/
theorem gcdSplit_second (a d : Nat) :
    (gcdSplit a d).2 = a / Nat.gcd a d := rfl

/-- 最大公約数と、その最大公約数で割った商との組から元の自然数を復元する。
原典：切り詰めた約数の評価。-/
theorem gcdSplit_recover (a d : Nat) :
    (gcdSplit a d).2 * (gcdSplit a d).1 = a := by
  simp only [gcdSplit]
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left a d)

/-- 最大公約数と商の組による写像は単射である。
原典：切り詰めた約数の評価。-/
theorem gcd_split_injective (d : Nat) :
    Function.Injective (fun a : Nat => gcdSplit a d) := by
  intro a b hab
  have h := congrArg (fun z : Nat × Nat => z.2 * z.1) hab
  calc
    a = (gcdSplit a d).2 * (gcdSplit a d).1 := (gcdSplit_recover a d).symm
    _ = (gcdSplit b d).2 * (gcdSplit b d).1 := h
    _ = b := gcdSplit_recover b d

/-- 二つの自然数が同じ自然数を割り切るなら、
一方を両者の最大公約数で割った商は、共通の倍数を他方で割った商を割り切る。
原典：切り詰めた約数の評価。-/
theorem div_gcd_dvd_quotient {a d n : Nat} (ha : a ∣ n) (hd : d ∣ n) :
    a / Nat.gcd a d ∣ n / d := by
  apply (Nat.dvd_div_iff_mul_dvd hd).2
  have hlcm : Nat.lcm a d = d * (a / Nat.gcd a d) := by
    rw [Nat.lcm_eq_mul_div, Nat.mul_comm a d,
      Nat.mul_div_assoc d (Nat.gcd_dvd_left a d)]
  rw [← hlcm]
  exact Nat.lcm_dvd ha hd

/-- 三つの自然数の最大公約数を順に取っても、
最後の二つの数の最大公約数を超えない。
原典：ヤコブスタール問題における剰余の評価。-/
theorem gcd_three_le_second (N x y : Nat) (hN : 0 < N) :
    Nat.gcd N (Nat.gcd x y) ≤ Nat.gcd y N := by
  apply Nat.le_of_dvd (Nat.gcd_pos_of_pos_right y hN)
  apply Nat.dvd_gcd
  · have h₁ := Nat.gcd_dvd_right N (Nat.gcd x y)
    have h₂ := Nat.gcd_dvd_right x y
    cases h₁ with
    | intro a ha =>
      cases h₂ with
      | intro b hb =>
        refine ⟨a * b, ?_⟩
        calc
          y = Nat.gcd x y * b := hb
          _ = (Nat.gcd N (Nat.gcd x y) * a) * b :=
            congrArg (fun z => z * b) ha
          _ = Nat.gcd N (Nat.gcd x y) * (a * b) :=
            Nat.mul_assoc _ _ _
  · exact Nat.gcd_dvd_left N (Nat.gcd x y)

/-- 除数１による切り上げ除算は元の自然数に等しい。-/
theorem ceilDiv_one (n : Nat) : ceilDiv n 1 = n := by
  simp [ceilDiv]

/-- 除数０による切り上げ除算は０とする。-/
theorem ceilDiv_zero (n : Nat) : ceilDiv n 0 = 0 := by
  simp [ceilDiv]

/-- 切り上げ除算の結果と除数の積は、分子に除数を加えて１を引いた数以下。-/
theorem ceilDiv_mul_le (n t : Nat) : ceilDiv n t * t ≤ n + t - 1 := by
  change ((n + t - 1) / t) * t ≤ n + t - 1
  exact Nat.div_mul_le_self (n + t - 1) t

/-- 正の除数で割った余りは、その除数より小さい。-/
theorem remainder_lt (a b : Nat) (hb : 0 < b) : a % b < b :=
  Nat.mod_lt a hb

/-- 被除数より小さい正の除数で割った余りは、
２倍しても元の被除数より小さい。
原典：量子因数分解における互除法の収束評価。-/
theorem euclid_two_halving {b r : Nat}
    (hr : 0 < r) (hrb : r < b) :
    2 * (b % r) < b := by
  by_cases h : 2 * r ≤ b
  · have hm := Nat.mod_lt b hr
    omega
  · have hb : b < 2 * r := by omega
    have hmod : b % r = b - r := by
      apply (Nat.mod_eq_sub_mod (Nat.le_of_lt hrb)).trans
      exact Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    omega

end ArithLemmas.Pure.Nat
