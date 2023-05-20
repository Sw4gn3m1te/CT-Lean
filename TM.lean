import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.List
import Mathlib.Data.Finset.Basic

universe u

section

variable (Q : Finset ℕ) [Inhabited Q] -- States
variable (Λ : Finset ℕ) [Inhabited Λ] -- Inp Alph
variable (Γ : Finset ℕ) [Inhabited Γ] -- Tape Alph
variable (F : Finset ℕ) [Inhabited F] -- Fin States

def powerset (s : Set α) : Set (Set α) :=
  { t | ∀ x, x ∈ t → x ∈ s }

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
  left : Array ℕ 
  right : Array ℕ

structure DTM where
  Q : Finset ℕ
  Λ : Finset ℕ
  Γ : Finset ℕ
  δ (q γ : ℕ) : Q × Γ × Direction
  F : Finset ℕ

inductive Machine
  | typeDTM : DTM → Machine
  | typeNTM : NTM → Machine

structure NTM where
  Q : Finset ℕ 
  Λ : Finset ℕ
  Γ : Finset ℕ 
  δ (q γ : ℕ) : Finset (Finset (Q × Γ × Direction))
  F : Finset ℕ

def cfgEquiv (c1 c2 : Cfg) : Prop :=
  c1.state = c2.state ∧ c1.head = c2.head ∧ c1.left = c2.left ∧ c1.right = c2.right

def updateHead (n: ℕ) (d: Direction) : ℕ :=
  match n, d with
    | 0, Direction.L => 0
    | _, Direction.R => n+1
    | _, Direction.L => n-1
    | _, Direction.N => n
  

def updateCfg (cfg: Cfg) (s: ℕ) (w: ℕ) (d: Direction) : Cfg := 
  match cfg.head, d with
    | 0, Direction.L => {state := s, head := 0, left := #[],  right := cfg.right.modify 0 w}
    | _, Direction.L => {state := s, head := cfg.head-1, left := cfg.left.pop,  right := cfg.left.insertAt 0 w}
    | _, Direction.R => {state := s, head := cfg.head+1, left := cfg.left.push w,  right := cfg.left.erase 1}
    | _, Direction.N => {state := s, head := cfg.head, left := cfg.left,  right := cfg.right.modify 0 w}


 -- how to make it s.t. it uses Machine ?
def step (M : DTM) (cfg : Cfg) : Cfg :=
  match (M.δ cfg.state cfg.right[0]!) with
    | (s, w, d) => updateCfg cfg s w d

def isFinal (M : DTM) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.F


-- run M from cfg for n steps
def runN (M : DTM) (cfg : Cfg) (n : ℕ) : Cfg :=
  if n = 0 then cfg
  else if (cfg.state ∈ M.F) then cfg 
  else runN M (step M cfg) (n-1)


def finiteReach (M : DTM) (c1 c2 : Cfg) : Prop :=
  ∃ (n : ℕ), cfgEquiv (runN M c1 n) c2

-- if c2 can be reached from c1 then there ex a sequence cs of configs from c1 to c2 (maybe emtpy if c2 is succ of c1)
theorem pathReachability : finiteReach M c1 c2 ↔ (∃ (cs : List Cfg), ∀ (c : Cfg), c ∈ cs → finiteReach M c c2) :=
  sorry

theorem DTMeqNTM : sorry :=
  sorry


