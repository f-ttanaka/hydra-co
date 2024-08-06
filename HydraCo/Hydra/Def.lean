import Batteries
import Mathlib.SetTheory.Lists
import Mathlib.Logic.Relation

open Nat

inductive Hydra : Type where
  | node : List Hydra → Hydra

open Hydra List

abbrev head := node []

-- List Hydra のような nest した構造に対する inductionのためのもの
def h_forall (P : Hydra → Prop) (hs : List Hydra) :=
  match hs with
  | [] => True
  | h :: hs' => P h ∧ h_forall P hs'

-- tree を、与えられた node から n個複製して生やす
-- n : replication parameter
def hcons_mult (h : Hydra) (n : Nat) (hs : List Hydra) : List Hydra :=
  List.append (List.replicate n h) hs

-- fold を使って定義すると停止性が認められず怒られてしまう
def hHeight (h : Hydra) :=
  match h with
  | node hs => hlMaxHeight hs
  where
    hlMaxHeight (hl : List Hydra) :=
    match hl with
    | [] => 0
    | sh :: hl' => max (1 + hHeight sh) (hlMaxHeight hl')

def hSize (h : Hydra) :=
  match h with
  | node hs => 1 + hlSizeSum hs
  where
    hlSizeSum (hl : List Hydra) :=
    match hl with
    | [] => 0
    | sh :: hl' => hSize sh + hlSizeSum hl'

def hMaxDegree (h : Hydra) :=
  match h with
  | node hs => max (List.length hs) (hlMaxDegree hs)
  where
    hlMaxDegree (hl : List Hydra) :=
      match hl with
      | [] => 0
      | sh :: hl' => max (hMaxDegree sh) (hlMaxDegree hl')

theorem height_lt_size : ∀ {h}, hHeight h < hSize h
  := by
  intro h
  induction h using Hydra.recOn
    (motive_2 := h_forall (fun x => hHeight x < hSize x))
  · rename_i hs IH
    induction hs
    · simp [hHeight, hHeight.hlMaxHeight, hSize]
    · rename_i h' hs' IHhs
      unfold h_forall at IH
      have IHf := IH.right
      have IHn := IHhs IHf
      simp [hHeight, hSize] at IHn
      simp [hHeight, hSize, hHeight.hlMaxHeight, hSize.hlSizeSum]
      apply And.intro
      · have IH_ieq := IH.left
        apply Nat.lt_add_right (hSize.hlSizeSum hs') IH_ieq
      · rw [Nat.add_left_comm]
        apply Nat.lt_add_left (hSize h') IHn
  · unfold h_forall
    apply True.intro
  · rename_i h t IHh IHt
    unfold h_forall
    apply And.intro; assumption; assumption

-- relations

-- binary relations Rel
abbrev Rel a := a → a → Prop

-- 根からの距離が 1 の頭部を切り落とすステップ R1
inductive S0 : Rel (List Hydra) where
  | S0_first : ∀ (hs), S0 (head :: hs) hs
  | S0_rest : ∀ (h hs hs'), S0 hs hs' → S0 (h :: hs) (h :: hs')

inductive R1 : Rel Hydra where
  | R1_intro : ∀ (h h'), S0 h h' → R1 (node h) (node h')

-- 根からの距離が 2 以上の頭部を切り落とすステップ R2
-- replication factor n に依存する

-- The proposition (S1 n s s') holds if s 0 is
-- obtained by replacing some element h of s by n + 1 copies of h 0
-- , where the
-- proposition (R1 h h') holds, in other words, h 0
-- is just h, without the choppedoff head.
inductive S1 (n : Nat) : Rel (List Hydra) where
  | S1_first : ∀ (hs h h'),
      R1 h h' →
      S1 n (h :: hs) (hcons_mult h' (succ n) hs)
  | S1_next : ∀ (h hs hs'),
      S1 n hs hs' →
      S1 n (h :: hs) (h :: hs')

mutual
inductive R2 (n : Nat) : Rel Hydra where
  | R2_intro : ∀ (h h'), S1 n h h' → R2 n (node h) (node h')
  | R2_intro_2 : ∀ (h h'), S2 n h h' → R2 n (node h) (node h')

inductive S2 (n : Nat) : Rel (List Hydra)
  | S2_first : ∀ (h h' hs),
      R2 n h h' →
      S2 n (h :: hs) (h' :: hs)
  | S2_next : ∀ (h r r'),
      S2 n r r' →
      S2 n (h :: r) (h :: r')
end

def roundN n h h' := R1 h h' ∨ R2 n h h'
def round h h' := ∃ n, roundN n h h'
infix:60 "-1->" => round

def roundPlus := Relation.TransGen round
def roundStar := Relation.ReflTransGen round
infix:60 "-+->" => roundPlus
infix:60 "-*->" => roundStar

-- Exercise 2.3
theorem S0_size_le : ∀ {hs hs'},
  S0 hs hs' → hHeight (node hs) ≥ hHeight (node hs')
  := by
  intro hs hs' H_S0; induction H_S0
  · rename_i hs
    simp [hHeight, hHeight.hlMaxHeight]
  · rename_i h hs hs' H_S0 IH
    simp [hHeight]
    simp [hHeight, hHeight.hlMaxHeight]
    apply Or.intro_right
    simp [hHeight]

theorem R1_size_le : ∀ {h h'},
  R1 h h' → hHeight h ≥ hHeight h'
  := by
  intro h h' H_R1
  cases H_R1
  rename_i _ _ H_S0
  apply S0_size_le H_S0

theorem S1_size_le : ∀ {n hs hs'},
  S1 n hs hs' → hSize (node hs) ≥ hSize (node hs')
  := by
  intro n hs hs' H_S1
  induction H_S1
  . rename_i hs h h' H_R1

example : ∀ {h h'},
  h -+-> h' → hHeight h ≥ hHeight h'
  := by
  intro h h' Hms
  induction Hms using Relation.TransGen.head_induction_on
  . rename_i g H1
