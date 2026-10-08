module

public import Mathlib.Data.Nat.ChineseRemainder

/-!
# 互いに素な法に対する中国剰余定理（第4段階4C）

Mathlib の `Nat.chineseRemainder` を基本実装として利用し、複数の合同条件を
一つの積の法へ統合する再利用可能な定理を揃える。
原典：`OAI/Combinatorics/Progressions/Lattices/ResidueSliceCountingCost.lean`、
`Mathlib/Data/Nat/ModEq.lean`。
-/

public section

namespace ArithLemmas.Mathlib.Nat

/-- 互いに素な二法による同時合同は、積を法とする単一の合同と同値である。 -/
theorem coprime_modEq_pair_iff (m n a b : ℕ) (h : m.Coprime n) :
    (a ≡ b [MOD m] ∧ a ≡ b [MOD n]) ↔ a ≡ b [MOD (m * n)] :=
  Nat.modEq_and_modEq_iff_modEq_mul h

/-- 互いに素な正の二法の任意の剰余には、積未満の同時解が存在する。 -/
theorem crt_exists_below (m n a b : ℕ) (h : m.Coprime n)
    (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ z : ℕ, z < m * n ∧ z ≡ a [MOD m] ∧ z ≡ b [MOD n] := by
  refine ⟨(Nat.chineseRemainder h a b : ℕ),
    Nat.chineseRemainder_lt_mul h a b hm hn,
    (Nat.chineseRemainder h a b).property.1,
    (Nat.chineseRemainder h a b).property.2⟩

/-- 二つの指定剰余を満たす任意の自然数はCRTの標準解と積の法で合同である。 -/
theorem crt_unique_mod_product (m n a b z : ℕ) (h : m.Coprime n)
    (ha : z ≡ a [MOD m]) (hb : z ≡ b [MOD n]) :
    z ≡ (Nat.chineseRemainder h a b : ℕ) [MOD (m * n)] :=
  Nat.chineseRemainder_modEq_unique h ha hb

/-- 積未満の範囲では、二つの合同条件を満たす自然数は一意である。 -/
theorem crt_unique_below (m n a b x y : ℕ) (h : m.Coprime n)
    (hx : x < m * n) (hy : y < m * n)
    (hxm : x ≡ a [MOD m]) (hxn : x ≡ b [MOD n])
    (hym : y ≡ a [MOD m]) (hyn : y ≡ b [MOD n]) : x = y := by
  have hm : x ≡ y [MOD m] := hxm.trans hym.symm
  have hn : x ≡ y [MOD n] := hxn.trans hyn.symm
  exact ((Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨hm, hn⟩).eq_of_lt_of_lt hx hy

/-- 両方の剰余が既知の代表元と一致することと、積を法とする合同が同値。 -/
theorem crt_constraints_iff (m n a b c x : ℕ) (h : m.Coprime n)
    (hca : c ≡ a [MOD m]) (hcb : c ≡ b [MOD n]) :
    (x ≡ a [MOD m] ∧ x ≡ b [MOD n]) ↔ x ≡ c [MOD (m * n)] := by
  rw [← Nat.modEq_and_modEq_iff_modEq_mul h]
  constructor
  · intro hx
    exact ⟨hx.1.trans hca.symm, hx.2.trans hcb.symm⟩
  · intro hx
    exact ⟨hx.1.trans hca, hx.2.trans hcb⟩

end ArithLemmas.Mathlib.Nat
