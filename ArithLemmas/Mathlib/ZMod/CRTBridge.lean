module

public import ArithLemmas.Mathlib.Nat.CRT
public import Mathlib.Data.ZMod.Basic

/-!
# 自然数の中国剰余定理とZModの橋渡し（第4段階4C）

合同条件を剰余環の等式へ翻訳する。ZModへの依存はMathlib層に限定する。
-/

public section

namespace ArithLemmas.Mathlib.ZMod

/-- 積を法とする二つの自然数の等式は、互いに素な二法での等式と同値である。 -/
theorem natCast_eq_mod_product_iff (m n a b : ℕ) (h : m.Coprime n) :
    ((a : ZMod (m * n)) = (b : ZMod (m * n))) ↔
      ((a : ZMod m) = (b : ZMod m)) ∧ ((a : ZMod n) = (b : ZMod n)) := by
  simp only [ZMod.natCast_eq_natCast_iff]
  exact (Nat.modEq_and_modEq_iff_modEq_mul h).symm

/-- CRTの標準解を各ZModへ写すと、指定した自然数の剰余と一致する。 -/
theorem crt_cast_left (m n a b : ℕ) (h : m.Coprime n) :
    (((Nat.chineseRemainder h a b : ℕ) : ZMod m) = (a : ZMod m)) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  exact (Nat.chineseRemainder h a b).property.1

/-- CRTの標準解を第二のZModへ写すと、第二の剰余と一致する。 -/
theorem crt_cast_right (m n a b : ℕ) (h : m.Coprime n) :
    (((Nat.chineseRemainder h a b : ℕ) : ZMod n) = (b : ZMod n)) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).2
  exact (Nat.chineseRemainder h a b).property.2

end ArithLemmas.Mathlib.ZMod
