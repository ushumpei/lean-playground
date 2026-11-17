/-
  ゼロから自分で定義するコース：総まとめ
  定義から囚人のジレンマの証明まで、自分のコードで埋める。
-/

-- 1. ゲームの定義
def Game (A B : Type) := A → B → Int × Int

-- 2. 均衡の定義
def IsNash (g : Game A B) (a : A) (b : B) : Prop :=
  (∀ a' :A, (g a' b).fst ≤ (g a b).fst) ∧ (∀ b' : B, (g a b').snd ≤ (g a b).snd)

-- 3. 行動の型
inductive Action where
  | cooperate
  | defect
open Action

-- 4. 囚人のジレンマ
def prisonersDilemma : Game Action Action :=
  fun a b =>
    match a, b with
    | cooperate, cooperate => (3, 3)
    | cooperate, defect    => (1, 4)
    | defect, cooperate    => (4, 1)
    | defect, defect       => (2, 2)

-- 5. 定理：自白・自白は均衡である
theorem defect_defect_isNash : IsNash prisonersDilemma defect defect :=
  And.intro (fun a' =>
    match a' with
    | cooperate =>
      -- (cooperate, defect).fst ≤ (defect, defect).fst を示す
      -- calc を使って証明する
      calc (prisonersDilemma cooperate defect).fst = 1 := rfl
        _ ≤ 2                                          := of_decide_eq_true rfl
        _ = (prisonersDilemma defect defect).fst       := rfl
    | defect =>
      -- (defect, defect).fst ≤ (defect, defect).fst を示す
      -- have を使って証明する
      have h: decide (2 ≤ 2) = true := rfl
      of_decide_eq_true h
  ) (fun b' =>
    match b' with
    | cooperate => of_decide_eq_true rfl
    | defect => of_decide_eq_true rfl
  )

theorem defect_defect_isNash_2 :
    IsNash prisonersDilemma defect defect := by
  refine ⟨?_, ?_⟩
  · intro a'
    cases a' <;> decide
  · intro b'
    cases b' <;> decide

def IsParetoImprovement (g : Game A B) (a : A) (b : B) (a' : A) (b' : B) : Prop :=
  ((g a b).fst ≤ (g a' b').fst ∧ (g a b).snd < (g a' b').snd) ∨
  ((g a b).fst < (g a' b').fst ∧ (g a b).snd ≤ (g a' b').snd)

def IsParetoOptimal (g : Game A B) (a : A) (b : B) : Prop :=
  (a' : A) → (b' : B) → IsParetoImprovement g a b a' b' → False
-- ∀ a' b', ¬ IsParetoImprovement g a b a' b' を書き換えた
-- ∀ a', … は fun a' => …
-- ¬P は P → False
