import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

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
  δ : Finset (ℕ × ℕ → ℕ × ℕ × Direction)

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
-- wut is reverse.tail.reverse bidde
def updateCfg (cfg: Cfg) (s w : ℕ) (d: Direction) : Cfg := 
  match cfg.head, d with
    | 0, Direction.L => {state := s, head := 0, left := List.nil,  right := cfg.right.modifyHead w}
    | _, Direction.L => {state := s, head := cfg.head-1, left := cfg.left.reverse.tail.reverse,  right := [w].append cfg.left}
    | _, Direction.R => {state := s, head := cfg.head+1, left := cfg.left.append [w],  right := cfg.left.tail}
    | _, Direction.N => {state := s, head := cfg.head, left := cfg.left,  right := cfg.right.modifyHead w}

def reachSucc (M : Machine) (c1 c2 : Cfg) : Prop :=
  ∃ (a γ s w : ℕ) (d : Direction), ∃ δ ∈ M.δ, δ (a, γ) = (s, w, d) ∧ cfgEquiv (updateCfg c1 s w d) c2 

def isAccept (M : Machine) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.Fₐ

def isReject (M : Machine) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.Fᵣ

def isFinal (M : Machine) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.Fₐ ∨ cfg.state ∈ M.Fᵣ


def languageofMachine (M : Machine)

--def reachN (M : Machine) (n : ℕ) (c1 c2 : Cfg) : Prop :=
--  if n = 0 then cfgEquiv c1 c2
--  else if n = 1 then reachSucc M c1 c2
--  else ∃ (c3 : Cfg), reachN M (n-1) c1 c3 ∧ reachN M (n-1) c3 c2


def reachN (M : Machine) (n : ℕ) (c1 c2 : Cfg) : Prop :=
  match n with
  | 0 => true
  | 1 => reachSucc M c1 c2
  | _ => ∃ (c : Cfg), reachN M (n - 1) c1 c ∧ reachSucc M c c2


def finiteReach (M : Machine) (c1 c2 : Cfg) : Prop :=
  ∃ (n : ℕ), reachN M n c1 c2


-- if c2 can be reached from c1 then there ex a sequence cs of configs from c1 to c2 (maybe emtpy if c2 is succ of c1)
theorem pathReachability : finiteReach M c1 c2 → (∃ (cs : List Cfg), ∀ (c : Cfg), c ∈ cs → finiteReach M c c2) := by
  intro h
  sorry

theorem finiteReachTrans (M : Machine) (c1 c2 c3 : Cfg) : (finiteReach M c1 c2 ∧ finiteReach M c2 c3) → (finiteReach M c1 c3) := by
  intro ⟨hr, n, hl⟩
  rw [finiteReach]
  induction n
  simp at hl
  sorry
  sorry
  


theorem addCompPathLen (n m : ℕ) (M : Machine) (c1 c2 c3 : Cfg) : reachN M n c1 c2 ∧ reachN M m c2 c3 ↔ reachN M (m+n) c1 c3 := by 
  constructor
  intro ⟨hrN, hrM⟩
  induction n
  rw [Nat.add_zero]
  simp at hrN
  sorry
  sorry
  sorry




