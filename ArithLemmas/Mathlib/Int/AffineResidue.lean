module

public import ArithLemmas.Mathlib.Int.ResidueInterval

/-!
# 一次合同条件のアフィン座標表示（第4段階4E-4）

整数区間内で指定した剰余類に属する点を、天井関数で指定される
整数添字の区間に対応させる。Mathlib の整数区間・合同類補題と、
4Bで証明済みの剰余類計数誤差評価を再利用する。

原典：`OAI/Combinatorics/Progressions/Lattices/ResidueSliceCountingCost.lean`
（`residueIndexLower`、`residueAffineEmbedding`、`residueIntervalEquiv`）。
-/

public section

namespace ArithLemmas.Mathlib.Int

/-- 区間の左端を通過する、合同類 `v` の最初の整数添字。 -/
@[expose] noncomputable def residueIndexLower (a r v : ℤ) : ℤ :=
  ⌈((a : ℚ) - (v : ℚ)) / (r : ℚ)⌉

/-- 両端に対応する整数添字の差を自然数として切り詰めた長さ。 -/
@[expose] noncomputable def residueIndexLength (a b r v : ℤ) : ℕ :=
  (residueIndexLower b r v - residueIndexLower a r v).toNat

/-- 非零の公差 `r` による整数のアフィン埋め込み。 -/
def residueAffineEmbedding (r v : ℤ) (hr : r ≠ 0) : ℤ ↪ ℤ where
  toFun k := v + r * k
  inj' _ _ h := mul_left_cancel₀ hr (add_left_cancel h)

/-- 添字区間を、その左端と長さによる表示に置き換える。 -/
theorem residueIndexInterval_eq (a b r v : ℤ) :
    Finset.Ico (residueIndexLower a r v) (residueIndexLower b r v) =
      Finset.Ico (residueIndexLower a r v)
        (residueIndexLower a r v + residueIndexLength a b r v) := by
  ext x
  simp only [Finset.mem_Ico, residueIndexLength]
  omega

/-- 指定剰余類の区間は、アフィン埋め込みで添字区間から得られる。 -/
theorem residueInterval_eq_map (a b r v : ℤ) (hr : 0 < r) :
    Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b) =
      (Finset.Ico (residueIndexLower a r v)
        (residueIndexLower a r v + residueIndexLength a b r v)).map
          (residueAffineEmbedding r v hr.ne') := by
  rw [Int.Ico_filter_modEq_eq, Int.Ico_filter_dvd_eq (a - v) (b - v) hr,
    Finset.map_map]
  simp only [Int.cast_sub]
  change (Finset.Ico (residueIndexLower a r v) (residueIndexLower b r v)).map _ = _
  rw [residueIndexInterval_eq]
  congr 1
  ext k
  change k * r + v = v + r * k
  ring

/-- 添字区間と指定剰余類の整数点の間の同値写像。 -/
noncomputable def residueIntervalEquiv (a b r v : ℤ) (hr : 0 < r) :
    ↥(Finset.Ico (residueIndexLower a r v)
        (residueIndexLower a r v + residueIndexLength a b r v)) ≃
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)) := by
  let f : ↥(Finset.Ico (residueIndexLower a r v)
      (residueIndexLower a r v + residueIndexLength a b r v)) →
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)) := fun x =>
    ⟨v + r * x.val, by
      rw [residueInterval_eq_map a b r v hr]
      exact Finset.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact (residueAffineEmbedding r v hr.ne').injective (congrArg Subtype.val h)
  · intro y
    have hyMap :
        y.val ∈ Finset.map (residueAffineEmbedding r v hr.ne')
          (Finset.Ico (residueIndexLower a r v)
            (residueIndexLower a r v +
              residueIndexLength a b r v)) := by
      rw [← residueInterval_eq_map a b r v hr]
      exact y.property
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hyMap
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

/-- アフィン同値写像の実際の整数値。 -/
@[simp] theorem residueIntervalEquiv_val (a b r v : ℤ) (hr : 0 < r)
    (x : ↥(Finset.Ico (residueIndexLower a r v)
      (residueIndexLower a r v + residueIndexLength a b r v))) :
    (residueIntervalEquiv a b r v hr x).val = v + r * x.val := by
  dsimp [residueIntervalEquiv, Equiv.ofBijective]


/-- 整数区間内の合同類の点数は、天井関数で定めた添字区間長に等しい。 -/
theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

/-- アフィン添字の長さと「区間幅／公差」の差は１以下。 -/
theorem residueIndexLength_absolute_error (a b r v : ℤ)
    (hab : a ≤ b) (hr : 0 < r) :
    |(residueIndexLength a b r v : ℝ) - ((b - a : ℤ) : ℝ) / (r : ℝ)| ≤ 1 := by
  rw [residueIndexLength_eq_card a b r v hr]
  exact residue_card_absolute_error a b r v hab hr

end ArithLemmas.Mathlib.Int
