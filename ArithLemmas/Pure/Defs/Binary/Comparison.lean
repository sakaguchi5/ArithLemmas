module

public import ArithLemmas.Pure.Defs.Binary.Representation

/-!
# 二進比較の薄い定義

OpenAI 原典の再帰的な二進比較を、計算モデルなしで自然数上に切り出す。
先頭が下位桁なので、末尾側（上位桁）の比較結果を優先する。
正当性・同値条件は導出層で証明する。
原典：`OAI/Analysis/MatrixSigning/Arithmetic/BinaryDivision.lean`。
-/

@[expose] public section

namespace ArithLemmas.Pure.Defs.Binary

/-- 二つの１桁の二進数字を比較した結果。 -/
def compareDigit (a b : Bool) : Ordering :=
  if a then (if b then .eq else .gt) else (if b then .lt else .eq)

/-- 下位桁が先頭の二進列を比較する。先行ゼロ（上位側のゼロ）も許す。 -/
def compareBits : List Bool → List Bool → Ordering
  | [], [] => .eq
  | [], b :: bs => match compareBits [] bs with
    | .eq => compareDigit false b
    | o => o
  | a :: as, [] => match compareBits as [] with
    | .eq => compareDigit a false
    | o => o
  | a :: as, b :: bs => match compareBits as bs with
    | .eq => compareDigit a b
    | o => o
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

/-- 比較結果が自然数の大小関係と一致するという命題。 -/
def OrderingCorrect (o : Ordering) (a b : Nat) : Prop :=
  match o with
  | .lt => a < b
  | .eq => a = b
  | .gt => b < a

end ArithLemmas.Pure.Defs.Binary
