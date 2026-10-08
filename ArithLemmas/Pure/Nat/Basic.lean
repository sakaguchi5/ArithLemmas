module

public import ArithLemmas.Pure.Defs.Nat.Basic

/-!
# 自然数の導出定理

追加の数学ライブラリを使わず、薄い定義の基本性質を証明する。
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

/-- 除数１による切り上げ除算は元の自然数に等しい。-/
theorem ceilDiv_one (n : Nat) : ceilDiv n 1 = n := by
  simp [ceilDiv]

/-- 除数０による切り上げ除算は０とする。-/
theorem ceilDiv_zero (n : Nat) : ceilDiv n 0 = 0 := by
  simp [ceilDiv]

end ArithLemmas.Pure.Nat
