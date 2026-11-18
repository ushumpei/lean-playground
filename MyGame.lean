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

theorem defect_defect_is_not_pareto_optimal : ¬ IsParetoOptimal prisonersDilemma defect defect :=
  fun h =>
  have h'  := h cooperate cooperate
  have h'' := Or.inl (
    And.intro (by calc
      (prisonersDilemma defect defect).fst = 2       := rfl
      _ ≤ 3                                          := of_decide_eq_true rfl
      _ = (prisonersDilemma cooperate cooperate).fst := rfl
    ) (
      by decide
    )
  )
  h' h''
/-
会話:
> me: h' h'' は absurd みたいなもの描かないんだね、なんかそんな記憶があったけど
> muse: はい、要りません [略...]
> me: P と \not P を使って False じゃない時でもゴールを作る感じか
> muse: その通りです。仕組みは2段になっています。
1段目：¬P は P → False なので、P と ¬P が両方あれば適用して False が作れます。
2段目：False はコンストラクタが1つもない型なので、False の値からは match の行き先として何でも作れます（False.elim）。前提が矛盾していれば結論は何でもよい、という爆発原理です。
absurd はこの2段をまとめたもので、中身はだいたい False.elim (hn h) です。
-/

theorem defect_defect_is_not_pareto_optimal2 : ¬ IsParetoOptimal prisonersDilemma defect defect :=
  fun h => h cooperate cooperate (by unfold IsParetoImprovement; decide)

#check @Int.not_lt
      -- Int.not_lt.mpr: b ≤ a → ¬ a < b
#check @Int.not_lt.mp
      -- Int.not_lt.mp: ¬ a < b → b ≤ a
#check @Int.not_lt.mpr
      -- Int.not_lt.mpr: b ≤ a → ¬ a < b
-- (3, 3) is Pareto optimal for the prisoners' dilemma
theorem cooperate_cooperate_is_pareto_optimal : IsParetoOptimal prisonersDilemma cooperate cooperate :=
  fun a' b' h => match a', b', h with
    -- (3, 3) vs (3, 3)
    | cooperate, cooperate, Or.inl ⟨_, hgt⟩ =>
      -- 丁寧に矛盾を示す

      -- 仮定より 3 < 3 となる
      have h_3gt3 : (3: Int) < 3 := hgt

      -- しかし当然 3 ≤ 3
      have h_3ge3 : (3: Int) ≤ 3 := by decide

      -- 3 ≤ 3 より 3 < 3 は成り立たない (a ≤ b → ¬ b < a)
      have h_not_3gt3 : ¬ ((3: Int) < 3) := (Int.not_lt.mpr h_3ge3)

      -- よって矛盾
      absurd h_3gt3 h_not_3gt3
    | cooperate, cooperate, Or.inr ⟨hgt, _⟩ =>
      -- 上の照明で必要だったのは仮定を正面から否定する命題 ¬ ((3: Int) < 3) で、これは何もなしに当然導ける
      have h_not_3lt3: ¬ ((3: Int) < 3) := Int.not_lt.mpr (by decide)
      -- よって矛盾
      absurd hgt h_not_3lt3
    -- (3, 3) vs (1, 4)
    | cooperate, defect, Or.inl ⟨hgte, _⟩ =>
      -- 完成版、仮定と当然導ける計算から矛盾を導く
      absurd hgte (by decide)
    | cooperate, defect, Or.inr ⟨hgt, _⟩ => absurd hgt (by decide)
    -- (3, 3) vs (4, 1)
    | defect, cooperate, h =>
      -- Or ごと計算して矛盾を導く
      absurd h (by
      -- ゴールは ¬ (IsParetoImprovement ...)
      -- unfold IsParetoImprovement でゴールを計算可能な形に展開
      -- ¬ ((prisonersDilemma ... ∧ (prisonersDilemma ...)) ∨ (...))
      unfold IsParetoImprovement
      -- 計算すると ¬ (3 ≤ 1)、これは 1 < 3 から導ける
      decide
    )
    -- (3, 3) vs (2, 2)
    | defect, defect, h => absurd h (by unfold IsParetoImprovement; decide)
