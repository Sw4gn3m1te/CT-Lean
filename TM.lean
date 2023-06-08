import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

import Language

universe u

section

--variable (Q : Finset ℕ) [Inhabited Q] -- States
--variable (Λ : Finset ℕ) [Inhabited Λ] -- Inp Alph
--variable (Γ : Finset ℕ) [Inhabited Γ] -- Tape Alph
--variable (F : Finset ℕ) [Inhabited F] -- Fin States

inductive Direction where
  | L : Direction
  | R : Direction
  | N : Direction


def directionToNum (d : Direction) : ℤ :=
  match d with
  | Direction.L => -1
  | Direction.R => 0
  | Direction.N => 1


-- cfg = [tl] q [tr], q points to the first elem of tr
-- hence inital config is [] q_0 [w] for some input w
structure Cfg where
  state : ℕ 
  head : ℕ
  left : List ℕ  
  right : List ℕ 

structure Machine where
  Q : Finset ℕ
  Λ : Finset ℕ 
  Γ : Finset ℕ 
  Fₐ : Finset ℕ
  Fᵣ : Finset ℕ 
  q0 : ℕ 
  δ : ℕ × ℕ → ℕ × ℕ × Direction

structure Dtm  extends Machine where

  uniqueness:
    ∀ x y : (ℕ × ℕ → ℕ × ℕ × Direction), 
      ∀ (a₁ a₂ : (ℕ × ℕ)), a₁ = a₂ ↔ x a₁ = y a₂


def cfgEquiv (c1 c2 : Cfg) : Prop :=
  c1.state = c2.state ∧ c1.head = c2.head ∧ c1.left = c2.left ∧ c1.right = c2.right

def updateHead (n: ℕ) (d: Direction) : ℕ :=
  match n, d with
    | 0, Direction.L => 0
    | _, Direction.R => n+1
    | _, Direction.L => n-1
    | _, Direction.N => n



-- creates new config by applying changes to old config
def updateCfg (cfg: Cfg) (s w : ℕ) (d: Direction) : Cfg := 
  match cfg.head, d with
    | 0, Direction.L => {state := s, head := 0, left := List.nil,  right := cfg.right.modifyHead w}
    | _, Direction.L => {state := s, head := cfg.head-1, left := cfg.left.reverse.tail.reverse,  right := [w].append cfg.left}
    | _, Direction.R => {state := s, head := cfg.head+1, left := cfg.left.append [w],  right := cfg.left.tail}
    | _, Direction.N => {state := s, head := cfg.head, left := cfg.left,  right := cfg.right.modifyHead w}

def reachSucc (M : Machine) (c1 c2 : Cfg) : Prop :=
  ∃ (a γ s w : ℕ) (d : Direction), M.δ (a, γ) = (s, w, d) ∧ cfgEquiv (updateCfg c1 s w d) c2 


def isAccept (M : Machine) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.Fₐ

def isReject (M : Machine) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.Fᵣ

def isFinal (M : Machine) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.Fₐ ∨ cfg.state ∈ M.Fᵣ



def reachN (M : Machine) (n : ℕ) (c1 c2 : Cfg) : Prop :=
  match n with
  | Nat.zero => true
  | Nat.succ m => ∃ (c : Cfg), (reachN M m c1 c ∧ reachSucc M c c2)



def finiteReach (M : Machine) (c1 c2 : Cfg) : Prop :=
  ∃ (n : ℕ), reachN M n c1 c2


theorem reach2IfReachSuccSucc (M : Machine) (c1 c2 c3 : Cfg) : reachSucc M c1 c2 ∧ reachSucc M c2 c3 → reachN M 2 c1 c3 := by
  intro ⟨hr, a, γ, s, w, d, hl⟩
  rw [reachN]
  use c2
  rw [reachN]
  constructor
  use c1
  rw [reachN]
  simp
  rw [reachSucc]
  rw [reachSucc] at hr
  exact hr
  rw [reachSucc]
  use a, γ, s, w, d
  exact hl


def MacceptsW (M : Machine) (w : Word) : Prop :=
  ∃ (c1 c2 : Cfg), finiteReach M c1 c2 ∧ isAccept M c2


def languageOfMachine (M : Machine)  : Language := 
  { w | ∃ (c1 c2 : Cfg) (tleft tright : Word) (s h : ℕ),
   (finiteReach M c1 c2 ∧ isAccept M c2 ∧ c2 = {state := s, head := h, left := tleft,  right := tright} ∧ w = tleft++tright)}

-- if c2 can be reached from c1 then there ex a sequence cs of configs from c1 to c2 (maybe emtpy if c2 is succ of c1)
theorem pathReachability (M : Machine) (c1 c2 : Cfg) : finiteReach M c1 c2 → (∃ (cs : List Cfg), ∀ (c : Cfg), c ∈ cs → finiteReach M c c2) := by
  sorry
  


theorem finiteReachIffReachN (c1 c2 : Cfg) (M : Machine) : finiteReach M c1 c2 ↔ ∃ (n : ℕ), reachN M n c1 c2 := by
  constructor
  intro ⟨n , h⟩
  use n
  exact h
  intro ⟨n ,h⟩
  rw [finiteReach]
  use n
  exact h


theorem finiteReachIffReachN2 (c1 c2 : Cfg) (M : Machine) (n : ℕ) : finiteReach M c1 c2 ↔ reachN M n c1 c2 := by
  constructor
  intro h
  rw [finiteReach] at h
  rcases n with ⟨zero, m⟩
  rfl
  sorry
  sorry


  

theorem finiteReachTrans (M : Machine) (c1 c2 c3 : Cfg) : (finiteReach M c1 c2 ∧ finiteReach M c2 c3) → (finiteReach M c1 c3) := by
  repeat rw [finiteReach]
  intro _
  constructor
  rw [reachN]


theorem addCompPathLen (M : Machine) (c1 c2 c3 : Cfg) : ∀ (n m : ℕ), (reachN M n c1 c2 ∧ reachN M m c2 c3 ↔ reachN M (m+n) c1 c3) := by 
  intro n m
  constructor
  intro ⟨hrN, hrM⟩
  induction n
  rw [Nat.add_zero]
  induction m
  rfl
  rw [reachN] at hrM
  use c2
  sorry
  rw [reachN] at hrN
  use c2
  sorry
  intro h
  rw [← finiteReachIffReachN2]
  sorry

