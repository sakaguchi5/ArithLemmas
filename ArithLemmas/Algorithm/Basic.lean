module

public import ArithLemmas.Pure.Nat.Basic
public import ArithLemmas.Tactic.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# ユークリッド互除法の計算手続き

薄い自然数定義として導入した反復手続きについて、
十分な反復回数の後には最大公約数と０が得られることを証明する。
原典：量子因数分解における互除法の回路。
-/
set_option linter.style.docString false

public section

namespace ArithLemmas.Algorithm

open ArithLemmas.Pure.Defs.Nat
open ArithLemmas.Pure.Nat
open ArithLemmas.Tactic.Nat

/-- 第２成分が２の指定冪より小さければ、
その指数の２倍以上の反復で最大公約数と０に到達する。
反復回数には余分な自然数を加えてもよい。-/
theorem euclidRun_terminal (s a b h : ℕ) (hb : b < 2 ^ s) :
    euclidRun (2 * s + h) a b = (Nat.gcd a b, 0) := by
  induction s generalizing a b h with
  | zero =>
    have hz : b = 0 := by simpa using hb
    subst b
    simp [euclidRun_zero]
  | succ s ih =>
    by_cases hb0 : b = 0
    · subst b
      simp [euclidRun_zero]
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    have he : 2 * (s + 1) + h = (2 * s + h + 1) + 1 := by omega
    by_cases hr0 : a % b = 0
    · rw [he, euclidRun, ite_eq_right hb0, hr0, euclidRun_zero]
      rw [Nat.gcd_comm a b, Nat.gcd_rec b a, hr0, Nat.gcd_zero_left]
    · have hr : 0 < a % b := Nat.pos_of_ne_zero hr0
      have hh := euclid_two_halving hr (Nat.mod_lt a hbpos)
      have hb' : b % (a % b) < 2 ^ s := by
        rw [pow_succ] at hb
        omega
      rw [he, euclidRun, ite_eq_right hb0, euclidRun,
        ite_eq_right hr0, ih _ _ h hb']
      congr 1
      calc
        Nat.gcd (a % b) (b % (a % b)) = Nat.gcd b (a % b) := by
          rw [Nat.gcd_comm (a % b) (b % (a % b)),
            ← Nat.gcd_rec (a % b) b, Nat.gcd_comm]
        _ = Nat.gcd a b := by
          rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm]

/-- 上の停止保証は、余分な反復を取らない場合にも成り立つ。-/
theorem euclidRun_terminal_exact (s a b : ℕ) (hb : b < 2 ^ s) :
    euclidRun (2 * s) a b = (Nat.gcd a b, 0) := by
  simpa using euclidRun_terminal s a b 0 hb

end ArithLemmas.Algorithm
