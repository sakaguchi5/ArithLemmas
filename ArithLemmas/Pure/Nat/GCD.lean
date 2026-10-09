module

public import ArithLemmas.Pure.Nat.Basic
public import ArithLemmas.Pure.Defs.Nat.GCDCoordinates

/-!
# GCD と原始座標への標準分解

自然数対の GCD 座標の像を完全に特徴付け、標準形との同値写像を構築する。
零対はただ一つの例外座標 `(0,0,0)` とする。残りは正の共通因子と
互いに素な二成分へ一意に分解される。復元・単射・計数保存はその系となる。
問題固有の複数の同義名を廃止し、一つの `gcdCoordinates` に統一する。
-/

public section

namespace ArithLemmas.Pure.Nat

open ArithLemmas.Pure.Defs.Nat

/-- Euclid の互除法を二度行っても GCD は変わらない。 -/
theorem gcd_two_reductions (a b : Nat) :
    Nat.gcd a b = Nat.gcd (a % b) (b % (a % b)) := by
  calc
    Nat.gcd a b = Nat.gcd (a % b) b := by
      rw [Nat.gcd_comm a b, Nat.gcd_rec b a]
    _ = Nat.gcd (a % b) (b % (a % b)) := by
      rw [Nat.gcd_rec (a % b) b, Nat.gcd_comm]

/-- 正の法を GCD で縮約しても商は正。 -/
theorem reduced_modulus_pos (a u : Nat) (hu : 0 < u) :
    0 < u / Nat.gcd a u :=
  Nat.div_pos (Nat.gcd_le_right a hu) (Nat.gcd_pos_of_pos_right a hu)

/-- GCD 座標の第一成分。 -/
theorem gcdCoordinates_gcd (v : Nat × Nat) :
    (gcdCoordinates v).1 = Nat.gcd v.1 v.2 := rfl

/-- 左成分の復元。 -/
theorem gcdCoordinates_recover_left (v : Nat × Nat) :
    (gcdCoordinates v).1 * (gcdCoordinates v).2.1 = v.1 := by
  change Nat.gcd v.1 v.2 * (v.1 / Nat.gcd v.1 v.2) = v.1
  simpa only [Nat.mul_comm] using Nat.div_mul_cancel (Nat.gcd_dvd_left v.1 v.2)

/-- 右成分の復元。 -/
theorem gcdCoordinates_recover_right (v : Nat × Nat) :
    (gcdCoordinates v).1 * (gcdCoordinates v).2.2 = v.2 := by
  change Nat.gcd v.1 v.2 * (v.2 / Nat.gcd v.1 v.2) = v.2
  simpa only [Nat.mul_comm] using Nat.div_mul_cancel (Nat.gcd_dvd_right v.1 v.2)

/-- 二成分の復元。 -/
theorem gcdCoordinates_recover (v : Nat × Nat) :
    (gcdCoordinates v).1 * (gcdCoordinates v).2.1 = v.1 ∧
    (gcdCoordinates v).1 * (gcdCoordinates v).2.2 = v.2 :=
  ⟨gcdCoordinates_recover_left v, gcdCoordinates_recover_right v⟩

/-- 零対は例外座標 `(0,0,0)` に対応する。 -/
theorem gcdCoordinates_zero : gcdCoordinates (0, 0) = (0, 0, 0) := by
  rfl

/-- 非零対の共通因子は正。 -/
theorem gcdCoordinates_gcd_pos_of_ne_zero (v : Nat × Nat)
    (hv : v ≠ (0, 0)) : 0 < (gcdCoordinates v).1 := by
  rcases v with ⟨a, b⟩
  change 0 < Nat.gcd a b
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      apply hv
      simp [ha, hb]
    exact Nat.gcd_pos_of_pos_right a (Nat.pos_of_ne_zero hb)
  · exact Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha)

/-- 非零対の二つの縮約座標は互いに素。 -/
theorem gcdCoordinates_coprime_of_ne_zero (v : Nat × Nat)
    (hv : v ≠ (0, 0)) :
    Nat.Coprime (gcdCoordinates v).2.1 (gcdCoordinates v).2.2 := by
  rcases v with ⟨a, b⟩
  have hg := gcdCoordinates_gcd_pos_of_ne_zero (a, b) hv
  change 0 < Nat.gcd a b at hg
  change Nat.Coprime (a / Nat.gcd a b) (b / Nat.gcd a b)
  exact Nat.coprime_div_gcd_div_gcd hg

/-- 正の共通因子と互いに素な二成分は既に標準形である。 -/
theorem gcdCoordinates_of_pos_coprime (g u v : Nat)
    (hg : 0 < g) (hc : Nat.Coprime u v) :
    gcdCoordinates (g * u, g * v) = (g, u, v) := by
  simp only [gcdCoordinates, Nat.gcd_mul_left, hc.gcd_eq_one,
    Nat.mul_one, Nat.mul_div_cancel_left _ hg]

/-- GCD 座標の像の完全な特徴付け。 -/
theorem gcdCoordinates_image_iff (w : Nat × Nat × Nat) :
    (∃ v : Nat × Nat, gcdCoordinates v = w) ↔
      w = (0, 0, 0) ∨
        (0 < w.1 ∧ Nat.Coprime w.2.1 w.2.2) := by
  constructor
  · rintro ⟨v, rfl⟩
    by_cases hv : v = (0, 0)
    · left
      simpa only [hv] using gcdCoordinates_zero
    · right
      exact ⟨gcdCoordinates_gcd_pos_of_ne_zero v hv,
        gcdCoordinates_coprime_of_ne_zero v hv⟩
  · intro hw
    rcases hw with hzero | ⟨hg, hc⟩
    · refine ⟨(0, 0), ?_⟩
      rw [hzero]
      exact gcdCoordinates_zero
    · refine ⟨(w.1 * w.2.1, w.1 * w.2.2), ?_⟩
      exact gcdCoordinates_of_pos_coprime w.1 w.2.1 w.2.2 hg hc

/-- 二つの型の間の双方向逆写像による同値。 -/
structure PureEquiv (α β : Type) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ x, invFun (toFun x) = x
  right_inv : ∀ y, toFun (invFun y) = y

/-- 自然数対と、唯一の零座標または原始 GCD 座標との同値写像。 -/
@[expose] def gcdCoordinatesEquiv :
    PureEquiv
      (Nat × Nat)
      {w : Nat × Nat × Nat //
        w = (0, 0, 0) ∨
          (0 < w.1 ∧ Nat.Coprime w.2.1 w.2.2)} where

  toFun v :=
    ⟨gcdCoordinates v,
      (gcdCoordinates_image_iff (gcdCoordinates v)).mp ⟨v, rfl⟩⟩

  invFun w :=
    (w.1.1 * w.1.2.1, w.1.1 * w.1.2.2)

  left_inv v := by
    apply Prod.ext
    · exact gcdCoordinates_recover_left v
    · exact gcdCoordinates_recover_right v

  right_inv w := by
    apply Subtype.ext
    rcases w.2 with hzero | ⟨hg, hc⟩
    · simp only [hzero, Nat.zero_mul]
      exact gcdCoordinates_zero
    · exact gcdCoordinates_of_pos_coprime
        w.1.1 w.1.2.1 w.1.2.2 hg hc

/-- 同値写像の順方向の写像は単射である。 -/
theorem PureEquiv.injective
    {α β : Type}
    (e : PureEquiv α β) :
    Function.Injective e.toFun := by
  intro x y h
  calc
    x = e.invFun (e.toFun x) := (e.left_inv x).symm
    _ = e.invFun (e.toFun y) := congrArg e.invFun h
    _ = y := e.left_inv y

/-- 単射性は標準形との同値写像から直ちに従う。 -/
theorem gcdCoordinates_injective : Function.Injective gcdCoordinates := by
  intro x y h
  apply gcdCoordinatesEquiv.injective
  apply Subtype.ext
  exact h

/-- 座標の等号は入力の等号と同値。 -/
theorem gcdCoordinates_eq_iff {v w : Nat × Nat} :
    gcdCoordinates v = gcdCoordinates w ↔ v = w := by
  constructor
  · intro h
    exact gcdCoordinates_injective h
  · intro h
    exact congrArg gcdCoordinates h

/-- 共通因子は左成分を割る。 -/
theorem gcdCoordinates_dvd_left (v : Nat × Nat) :
    (gcdCoordinates v).1 ∣ v.1 :=
  Nat.gcd_dvd_left v.1 v.2

/-- 共通因子は右成分を割る。 -/
theorem gcdCoordinates_dvd_right (v : Nat × Nat) :
    (gcdCoordinates v).1 ∣ v.2 :=
  Nat.gcd_dvd_right v.1 v.2

/-- 左成分が正なら共通因子はそれを超えない。 -/
theorem gcdCoordinates_gcd_le_left {a b : Nat} (ha : 0 < a) :
    (gcdCoordinates (a, b)).1 ≤ a :=
  Nat.gcd_le_left b ha

/-- 右成分が正なら共通因子はそれを超えない。 -/
theorem gcdCoordinates_gcd_le_right {a b : Nat} (hb : 0 < b) :
    (gcdCoordinates (a, b)).1 ≤ b :=
  Nat.gcd_le_right a hb

/-- 左縮約商は元の数を超えない。 -/
theorem gcdCoordinates_left_quotient_le (v : Nat × Nat) :
    (gcdCoordinates v).2.1 ≤ v.1 :=
  Nat.div_le_self v.1 (Nat.gcd v.1 v.2)

/-- 右縮約商は元の数を超えない。 -/
theorem gcdCoordinates_right_quotient_le (v : Nat × Nat) :
    (gcdCoordinates v).2.2 ≤ v.2 :=
  Nat.div_le_self v.2 (Nat.gcd v.1 v.2)

/-- 正の左成分に対して共通因子は正。 -/
theorem gcdCoordinates_pos_of_left {a b : Nat} (ha : 0 < a) :
    0 < (gcdCoordinates (a, b)).1 :=
  Nat.gcd_pos_of_pos_left b ha

/-- 正の右成分に対して共通因子は正。 -/
theorem gcdCoordinates_pos_of_right {a b : Nat} (hb : 0 < b) :
    0 < (gcdCoordinates (a, b)).1 :=
  Nat.gcd_pos_of_pos_right a hb

/-- 正の左成分の縮約商は正。 -/
theorem gcdCoordinates_left_quotient_pos {a b : Nat} (ha : 0 < a) :
    0 < (gcdCoordinates (a, b)).2.1 :=
  Nat.div_pos (Nat.gcd_le_left b ha) (Nat.gcd_pos_of_pos_left b ha)

/-- 正の右成分の縮約商は正。 -/
theorem gcdCoordinates_right_quotient_pos {a b : Nat} (hb : 0 < b) :
    0 < (gcdCoordinates (a, b)).2.2 :=
  reduced_modulus_pos a b hb

end ArithLemmas.Pure.Nat
