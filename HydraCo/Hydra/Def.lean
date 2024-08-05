import Batteries
import Mathlib.SetTheory.Lists
open Nat

inductive Hydra : Type where
  | node : List Hydra → Hydra

open Hydra List

-- List Hydra のような nest した構造に対する inductionのためのもの
def h_forall (P : Hydra → Prop) (hs : List Hydra) :=
  match hs with
  | [] => True
  | h :: hs' => P h ∧ h_forall P hs'

-- tree を、与えられた node から n個複製して生やす
-- n : replication parameter
def hydra_mult (h : Hydra) (n : Nat) (hs : List Hydra) : List Hydra :=
  match n with
  | zero => hs
  | succ m => h :: (hydra_mult h m hs)

-- fold を使って定義すると停止性が認められず怒られてしまう
def hHeight (h : Hydra) :=
  match h with
  | node hs => (hlMaxHeight hs)
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
