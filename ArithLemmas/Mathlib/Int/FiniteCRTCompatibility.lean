module

public import ArithLemmas.Mathlib.Int.FiniteCRT
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Algebra.GCDMonoid.FinsetLemmas

/-!
# 有限族の一般化中国剰余定理：GCD整合性の必要十分条件

正の自然数を法とする有限族の合同条件に対して、
任意の二条件がその法の GCD に関して整合することと、
全条件を満たす整数が存在することの同値を証明する。

核となる数学は `gcd(a, lcmᵢ mᵢ) = lcmᵢ gcd(a, mᵢ)` である。
この分配則は Mathlib の素因数分解の指数公式から導く。
二法の存在定理は既存の `crt_exists_iff_gcd` を再利用する。

その結果、同時解の存在・LCM合同類による全解集合・
有限区間における正確な解の個数が一つの条件で特徴付けられる。
-/

public section

namespace ArithLemmas.Mathlib.Int

variable {ι : Type*}

/-- 整数上の有限 LCM と自然数上の有限 LCM は、自然数キャストで可換。 -/
theorem finiteCRT_lcm_natCast (s : Finset ι) (m : ι → ℕ) :
    s.lcm (fun i => (m i : ℤ)) = ((s.lcm m : ℕ) : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert i s hi ih =>
      simp only [Finset.lcm_insert, ih]
      rfl

/-- GCD は有限 LCM に分配する（対象の自然数と全ての法が正の場合）。 -/
theorem finiteCRT_gcd_lcm_distrib (s : Finset ι) (m : ι → ℕ) (a : ℕ)
    (ha : 0 < a) (hm : ∀ i ∈ s, 0 < m i) :
    Nat.gcd a (s.lcm m) = s.lcm (fun i => Nat.gcd a (m i)) := by
  classical
  have hL : s.lcm m ≠ 0 :=
    (Finset.lcm_ne_zero_iff).2 (fun i hi => (hm i hi).ne')
  have hR : s.lcm (fun i => Nat.gcd a (m i)) ≠ 0 :=
    (Finset.lcm_ne_zero_iff).2 (fun i hi =>
      (Nat.gcd_pos_of_pos_left (m i) ha).ne')
  have hleft : Nat.gcd a (s.lcm m) ≠ 0 :=
    (Nat.gcd_pos_of_pos_left _ ha).ne'
  apply Nat.eq_of_factorization_eq hleft hR
  intro p
  calc
    (Nat.gcd a (s.lcm m)).factorization p =
        a.factorization p ⊓ (s.lcm m).factorization p := by
          rw [Nat.factorization_gcd ha.ne' hL, Finsupp.inf_apply]
    _ = a.factorization p ⊓
          (s.sup fun i => (m i).factorization p) := by
          rw [Finset.factorization_lcm
            (fun i hi => (hm i hi).ne') p]
    _ = s.sup (fun i =>
          a.factorization p ⊓ (m i).factorization p) := by
          exact Finset.sup_inf_distrib_left
            s
            (fun i => (m i).factorization p)
            (a.factorization p)
    _ = (s.lcm (fun i => Nat.gcd a (m i))).factorization p := by
          rw [Finset.factorization_lcm
            (fun i hi =>
              (Nat.gcd_pos_of_pos_left (m i) ha).ne') p]
          apply Finset.sup_congr rfl
          intro i hi
          rw [Nat.factorization_gcd ha.ne' (hm i hi).ne',
            Finsupp.inf_apply]
/--
有限族の合同条件を満たす整数 `c` と、新しい合同条件の剰余 `r i` が、
各既存の法との GCD に関して整合しているなら、
`c` と `r i` は既存の法の LCM と新しい法の GCD に関しても整合する。

有限 CRT の帰納段階で、二法 CRT を適用するための整合条件を与える。
-/
theorem finiteCRT_extend_compatible
    (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ)
    (i : ι) (c : ℤ)
    (hmi : 0 < m i)
    (hmS : ∀ j ∈ s, 0 < m j)
    (hc : ∀ j ∈ s, c ≡ r j [ZMOD (m j : ℤ)])
    (hp : ∀ j ∈ s,
      r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)]) :
    c ≡ r i
      [ZMOD (Nat.gcd (s.lcm m) (m i) : ℤ)] := by
  have hgcd_dvd_diff : ∀ j ∈ s,
      (Nat.gcd (m i) (m j) : ℤ) ∣ r i - c := by
    intro j hj
    have hpair :
        (Nat.gcd (m i) (m j) : ℤ) ∣ r j - r i :=
      Int.modEq_iff_dvd.mp (hp j hj)
    have hgj :
        (Nat.gcd (m i) (m j) : ℤ) ∣ (m j : ℤ) := by
      exact_mod_cast Nat.gcd_dvd_right (m i) (m j)
    have hcj :
        (Nat.gcd (m i) (m j) : ℤ) ∣ r j - c :=
      hgj.trans (Int.modEq_iff_dvd.mp (hc j hj))
    convert dvd_sub hcj hpair using 1
    ring
  have hlcm_dvd_diff :
      (s.lcm (fun j =>
        (Nat.gcd (m i) (m j) : ℤ))) ∣ r i - c :=
    (Finset.lcm_dvd_iff).2 hgcd_dvd_diff
  have hlcm_eq_gcd :
      s.lcm (fun j =>
        (Nat.gcd (m i) (m j) : ℤ)) =
          (Nat.gcd (s.lcm m) (m i) : ℤ) := by
    rw [finiteCRT_lcm_natCast]
    exact congrArg (fun z : ℕ => (z : ℤ))
      ((finiteCRT_gcd_lcm_distrib s m (m i) hmi hmS).symm.trans
        (Nat.gcd_comm (m i) (s.lcm m)))
  exact Int.modEq_iff_dvd.mpr
    (hlcm_eq_gcd ▸ hlcm_dvd_diff)

/--
正の自然数を法とする有限族の合同条件について、
全条件を満たす整数が存在することと、
任意の二条件がそれぞれの法の GCD に関して整合することは同値である。

十分性は有限集合に関する帰納法で証明する。
既存の合同条件と新しい条件の整合性は
`finiteCRT_extend_compatible` から導き、
二法の中国剰余定理 `crt_exists_iff_gcd` を適用する。
-/
theorem finiteCRT_exists_iff_pairwise_gcd (s : Finset ι)
    (m : ι → ℕ) (r : ι → ℤ)
    (hm : ∀ i ∈ s, 0 < m i) :
    (∃ c : ℤ, ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)]) ↔
      ∀ i ∈ s, ∀ j ∈ s,
        r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)] := by
  constructor
  · exact finiteCRT_pairwise_necessary s m r
  · intro hp
    classical
    revert hm hp
    induction s using Finset.induction_on with
    | empty =>
        intro _ _
        exact ⟨0, by simp⟩
    | @insert i s hi ih =>
        intro hm hp
        have hmS : ∀ j ∈ s, 0 < m j :=
          fun j hj => hm j (Finset.mem_insert_of_mem hj)
        have hpS : ∀ j ∈ s, ∀ k ∈ s,
            r j ≡ r k [ZMOD (Nat.gcd (m j) (m k) : ℤ)] := by
          intro j hj k hk
          exact hp j (Finset.mem_insert_of_mem hj)
            k (Finset.mem_insert_of_mem hk)
        obtain ⟨c, hc⟩ := ih hmS hpS
        -- 新しい条件と既存の各条件との GCD 整合性
        have hpNew : ∀ j ∈ s,
            r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)] := by
          intro j hj
          exact hp i (Finset.mem_insert_self i s)
            j (Finset.mem_insert_of_mem hj)
        -- 既存の LCM と新しい法との GCD 整合性
        have hcompat :
            c ≡ r i
              [ZMOD (Nat.gcd (s.lcm m) (m i) : ℤ)] :=
          finiteCRT_extend_compatible s m r i c
            (hm i (Finset.mem_insert_self i s))
            hmS hc hpNew
        -- 二法 CRT により、新しい共通解を構成
        obtain ⟨d, hdL, hdi⟩ :=
          (crt_exists_iff_gcd (s.lcm m) (m i) c (r i)).mpr hcompat
        -- 構成した整数がすべての条件を満たすことを確認
        refine ⟨d, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hdi
        · have hjs :
              (m j : ℤ) ∣ ((s.lcm m : ℕ) : ℤ) := by
            exact_mod_cast
              (Finset.dvd_lcm (s := s) (f := m) hj)
          have hdj :
              d ≡ c [ZMOD (m j : ℤ)] :=
            Int.modEq_iff_dvd.mpr
              (hjs.trans (Int.modEq_iff_dvd.mp hdL))
          exact hdj.trans (hc j hj)

/-- GCD の対ごとの整合条件だけで、全解集合は LCM 合同類になる。 -/
theorem finiteCRT_coset_iff_pairwise_gcd (s : Finset ι)
    (m : ι → ℕ) (r : ι → ℤ)
    (hm : ∀ i ∈ s, 0 < m i) :
    (∃ c : ℤ, ∀ x : ℤ,
      (∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)]) ↔
        x ≡ c [ZMOD s.lcm (fun i => (m i : ℤ))]) ↔
      ∀ i ∈ s, ∀ j ∈ s,
        r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)] := by
  exact (finiteCRT_coset_iff_exists s (fun i => (m i : ℤ)) r).trans
    (finiteCRT_exists_iff_pairwise_gcd s m r hm)

/--
有限族の法がすべて正で、剰余が対ごとに GCD 整合条件を満たすなら、
全合同条件を満たす整数 `c` が存在し、任意の整数区間 `[a, b)` に
含まれる同時解の個数は、法の LCM と代表元 `c` を用いて正確に計算できる。

具体的には、次の二つを同時に保証する。

1. `c` はすべての合同条件を満たす。
2. 区間 `[a, b)` 内の同時解の個数は、
   `residueIndexLength a b L c` に等しい。
   ここで `L` はすべての法の最小公倍数である。

この定理は、GCD 整合条件による共通解の存在定理と、
既存の有限 CRT の正確な区間計数定理から導出する。
-/
theorem finiteCRT_count_exact_of_pairwise_gcd (s : Finset ι)
    (m : ι → ℕ) (r : ι → ℤ) (a b : ℤ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hp : ∀ i ∈ s, ∀ j ∈ s,
      r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)]) :
    ∃ c : ℤ,
      (∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)]) ∧
      (Finset.filter
        (fun x : ℤ => ∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)])
        (Finset.Ico a b)).card =
          residueIndexLength a b
            (s.lcm (fun i => (m i : ℤ))) c := by
  obtain ⟨c, hc⟩ :=
    (finiteCRT_exists_iff_pairwise_gcd s m r hm).mpr hp
  refine ⟨c, hc, ?_⟩
  exact finiteCRT_count_exact
    s (fun i => (m i : ℤ)) r a b c
    (fun i hi => by exact_mod_cast hm i hi) hc

/-- 対ごとの GCD 整合条件から、区間内の同時解の
個数と周期長による期待値との差が 1 以下であることを導く。 -/
theorem finiteCRT_count_error_of_pairwise_gcd (s : Finset ι)
    (m : ι → ℕ) (r : ι → ℤ) (a b : ℤ)
    (hab : a ≤ b) (hm : ∀ i ∈ s, 0 < m i)
    (hp : ∀ i ∈ s, ∀ j ∈ s,
      r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)]) :
    |((Finset.filter
        (fun x : ℤ => ∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)])
        (Finset.Ico a b)).card : ℝ) -
        ((b - a : ℤ) : ℝ) /
          ((s.lcm (fun i => (m i : ℤ)) : ℤ) : ℝ)| ≤ 1 := by
  obtain ⟨c, hc⟩ :=
    (finiteCRT_exists_iff_pairwise_gcd s m r hm).mpr hp
  have hmInt : ∀ i ∈ s, 0 < (m i : ℤ) := by
    intro i hi
    exact_mod_cast hm i hi
  exact finiteCRT_count_error
    s (fun i => (m i : ℤ)) r a b c hab hmInt hc

/-- 対ごとの整合性が成立しなければ、どの整数区間でも同時解は存在しない。 -/
theorem finiteCRT_count_zero_of_not_pairwise_gcd (s : Finset ι)
    (m : ι → ℕ) (r : ι → ℤ) (a b : ℤ)
    (hm : ∀ i ∈ s, 0 < m i)
    (hbad : ¬ ∀ i ∈ s, ∀ j ∈ s,
      r i ≡ r j [ZMOD (Nat.gcd (m i) (m j) : ℤ)]) :
    (Finset.filter
      (fun x : ℤ => ∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)])
      (Finset.Ico a b)).card = 0 := by
  classical
  have hno : ¬ ∃ c : ℤ, ∀ i ∈ s, c ≡ r i [ZMOD (m i : ℤ)] := by
    intro h
    exact hbad ((finiteCRT_exists_iff_pairwise_gcd s m r hm).mp h)
  have hempty :
      Finset.filter (fun x : ℤ => ∀ i ∈ s,
          x ≡ r i [ZMOD (m i : ℤ)]) (Finset.Ico a b) = ∅ := by
    ext x
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hx
    exact (hno ⟨x, hx.2⟩).elim
  simp [hempty]

end ArithLemmas.Mathlib.Int
