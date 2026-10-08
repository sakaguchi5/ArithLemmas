import ArithLemmas.Mathlib.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# 剰余環における自然数の桁

自然数の剰余計算と、剰余環における可逆性を結び付ける。
原典：ハイルブロン三角形問題における桁の符号化。
-/
set_option linter.style.docString false

namespace ArithLemmas.Mathlib.ZMod

open ArithLemmas.Mathlib.Finset

/-- 自然数の加算は剰余環への写像で保存される。-/
theorem natCast_add (m a b : ℕ) :
    ((a + b : ℕ) : ZMod m) = (a : ZMod m) + (b : ZMod m) := by
  simp

/-- 自然数の乗算は剰余環への写像で保存される。-/
theorem natCast_mul (m a b : ℕ) :
    ((a * b : ℕ) : ZMod m) = (a : ZMod m) * (b : ZMod m) := by
  simp

/-- 最下位の桁が０でも基数の倍数でもなければ、
素数冪を法とする剰余環では、桁から作った数が可逆になる。-/
theorem baseValue_isUnit {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : ℕ → ℕ) (hzero : 0 < digit 0) (hsmall : digit 0 < B) :
    IsUnit (baseValue B k digit : ZMod (B ^ k)) := by
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow hB hk).2
  intro hdiv
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  rw [baseValue_mod B k digit hk, Nat.mod_eq_of_lt hsmall] at hm
  omega

/-- 全ての桁が所定の範囲内にある場合も、最下位桁の条件から可逆性を得られる。-/
theorem baseValue_isUnit_of_digit_bounds {B k L : ℕ} (hB : B.Prime)
    (hk : 0 < k) (hLB : L < B) (digit : ℕ → ℕ)
    (hdigit : ∀ i < k, 1 ≤ digit i ∧ digit i ≤ L) :
    IsUnit (baseValue B k digit : ZMod (B ^ k)) := by
  exact baseValue_isUnit hB hk digit (hdigit 0 hk).1
    (lt_of_le_of_lt (hdigit 0 hk).2 hLB)

end ArithLemmas.Mathlib.ZMod
