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

-- 4. 囚人のジレンマ
def prisonersDilemma : Game Action Action :=
  fun a b =>
    match a, b with
    | Action.cooperate, Action.cooperate => (3, 3)
    | Action.cooperate, Action.defect    => (1, 4)
    | Action.defect, Action.cooperate    => (4, 1)
    | Action.defect, Action.defect       => (2, 2)

-- 5. 定理：自白・自白は均衡である
theorem defect_defect_isNash : IsNash prisonersDilemma Action.defect Action.defect :=
  And.intro (fun a' =>
    match a' with
    | Action.cooperate =>
      -- (cooperate, defect).fst ≤ (defect, defect).fst を示す
      -- calc を使って証明する
      calc (prisonersDilemma Action.cooperate Action.defect).fst = 1 := rfl
        _ ≤ 2                                                        := of_decide_eq_true rfl
        _ = (prisonersDilemma Action.defect Action.defect).fst       := rfl
    | Action.defect =>
      -- (defect, defect).fst ≤ (defect, defect).fst を示す
      -- have を使って証明する
      have h: decide (2 ≤ 2) = true := rfl
      of_decide_eq_true h
  ) (fun b' =>
    match b' with
    | Action.cooperate => of_decide_eq_true rfl
    | Action.defect => of_decide_eq_true rfl
  )
