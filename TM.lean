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
  F : Finset ℕ
  q0 : ℕ 
  δ : ℕ × ℕ → ℕ × ℕ × Direction

  --FInQ:
  --  ∀ q : ℕ, q ∈ F → q ∈ Q
  

structure Dtm  extends Machine where

  uniqueness:
    ∀ x y : (ℕ × ℕ → ℕ × ℕ × Direction), 
      ∀ (a b : (ℕ × ℕ)), a = b ↔ x a = y b


def startCfg (M : Machine) (w : Word) : Cfg := 
  {state:=M.q0, head:=0, left:=List.nil, right:=w}


-- lets assume M1.Q ∩ M2.Q = ∅ 
-- then use gödel numbering for states 
def prodTm (M1 M2 : Machine) : Machine :=
  {Q := (Finset.product M1.Q M2.Q).image (fun n : ℕ × ℕ => 2 ^ n.1 * 3 ^ n.2),
   Λ := M1.Λ ∪ M2.Λ, Γ := M1.Γ ∪ M2.Γ,
   F := (Finset.product (M1.F ∩ M2.F) (M1.F ∩ M2.F)).image (fun n : ℕ × ℕ => 2 ^ n.1 * 3 ^ n.2) , q0 := 2^M1.q0*2^M2.q0, δ:=M1.δ}

  
def TMExample : Machine := {Q:= Finset.range 3, Λ:= Finset.range 3, Γ:= Finset.range 3, F:= Finset.empty, q0:= 1,
                            δ := fun (q, γ) => ((q + 1) % 5, (γ + 1) % 26, Direction.L)}

def TMExample2 : Machine := {Q:= Finset.range 4, Λ:= Finset.range 4, Γ:= Finset.range 4, F:= Finset.empty, q0:= 1,
                             δ := fun (q, γ) => ((q + 1) % 5, (γ + 1) % 26, Direction.L)}


def coTm (M : Machine) : Machine :=
  {Q:=M.Q, Λ:=M.Λ, Γ:=M.Γ, F:=(M.Q \ M.F), q0:=M.q0, δ:=M.δ}


theorem mExpand (M : Machine) : M = { Q := M.Q, Λ := M.Λ, Γ := M.Γ, F := M.F, q0 := M.q0, δ := M.δ } := by
  sorry

theorem mEqCoCoM (M : Machine) : M = coTm (coTm M) := by
  repeat rw [coTm]
  simp
  -- needs FInQ 
  sorry

def cfgEquiv (c1 c2 : Cfg) : Prop :=
  c1.state = c2.state ∧ c1.head = c2.head ∧ c1.left = c2.left ∧ c1.right = c2.right


@[simp]
theorem reflCfgEquiv (c : Cfg) : cfgEquiv c c := by
  rw [cfgEquiv]
  simp


@[simp]
theorem symCfgEquiv (c1 c2 : Cfg) : cfgEquiv c1 c2 ↔ cfgEquiv c2 c1 := by
  constructor
  intro h
  rw [cfgEquiv] at h
  rw [cfgEquiv]
  tauto
  intro h
  rw [cfgEquiv] at h
  rw [cfgEquiv]
  tauto


@[simp]
theorem transCfgEquiv (c1 c2 c3 : Cfg) : cfgEquiv c1 c2 ∧ cfgEquiv c2 c3 → cfgEquiv c1 c3 := by
  intro ⟨hl, hr⟩
  rw [cfgEquiv]
  rw [cfgEquiv] at hl
  rw [cfgEquiv] at hr
  rcases hl with ⟨s_left, h_left, l_left, r_left⟩
  rcases hr with ⟨s_right, h_right, l_right, r_right⟩
  constructor
  rw [s_left]
  rw [s_right]
  constructor
  rw [h_left]
  rw [h_right]
  constructor
  rw [l_left]
  rw [l_right]
  rw [r_left]
  rw [r_right]


theorem cfgEquivIffEq (c1 c2 : Cfg) : cfgEquiv c1 c2 ↔ c1 = c2 := by
  sorry

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

--def reachSuccOld (M : Machine) (c1 c2 : Cfg) : Prop :=
--  ∃ (a γ s w : ℕ) (d : Direction), M.δ (a, γ) = (s, w, d) ∧ cfgEquiv (updateCfg c1 s w d) c2 


def reachSucc (M : Machine) (c1 c2 : Cfg) : Prop :=
  ∃ (s w : ℕ) (d : Direction), M.δ (c1.state, c1.right.head!) = (s, w, d) ∧ cfgEquiv (updateCfg c1 s w d) c2 

def isAccept (M : Machine) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.F ∧ cfg.state ∈ M.Q

def isReject (M : Machine) (cfg : Cfg)  : Prop :=
  cfg.state ∉ M.F ∧ cfg.state ∈ M.Q

-- just stand still if term ?
def isFinal (M  : Machine) (cfg : Cfg) : Prop :=
  M.δ (cfg.state, cfg.right.head!) = (cfg.state, cfg.right.head!, Direction.N)


def reachN (M : Machine) (n : ℕ) (c1 c2 : Cfg) : Prop :=
  match n with
  | 0 => cfgEquiv c1 c2
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


def mAcceptsW (M : Machine) (w : Word) : Prop :=
  ∃ (c1 c2 : Cfg), c1 = startCfg M w ∧ finiteReach M c1 c2 ∧ isAccept M c2 ∧ isFinal M c2

def mRejectsW (M : Machine) (w : Word) : Prop :=
  ∃ (c1 c2 : Cfg), c1 = startCfg M w ∧ finiteReach M c1 c2 ∧ isReject M c2 ∧ isFinal M c2
 
def languageOfMachine (M : Machine)  : Language := 
  { w | mAcceptsW M w}

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
  

theorem reach0EqCfgEquiv (M : Machine) (c1 c2 : Cfg) : reachN M 0 c1 c2 ↔ cfgEquiv c1 c2 := by
  constructor
  rw [reachN]
  simp
  rw [reachN]
  simp

theorem reachNPlusOne (M : Machine) (c1 c3 : Cfg) (n : ℕ) : (∃ (c : Cfg), (reachN M n c1 c ∧ reachSucc M c c3)) ↔ reachN M (Nat.succ n) c1 c3 := by
  constructor
  intro h
  rw [reachN]
  exact h
  intro h
  rw [reachN] at h
  exact h

lemma natSucc (m n : ℕ) : (Nat.succ m + n) = (Nat.succ (m + n)) := by
  simp_arith

lemma natSucc2 (m n : ℕ) : (n + Nat.succ m) = (Nat.succ (n + m)) := by
  simp_arith

theorem addCompPathLen2 (M : Machine) (c1 c2 c3 : Cfg) (m n : ℕ) :  (∃ c2, (reachN M m c1 c2 ∧ reachN M n c2 c3)) → reachN M (m + n) c1 c3 := by 
  intro h
  rcases h with ⟨c, hl, hr⟩
  induction n generalizing c3 with
    | zero =>
      simp
      rw [reachN] at hr
      rw [cfgEquivIffEq] at hr
      rw [← hr]
      exact hl
    | succ m ih =>
      rw [natSucc2, reachN]
      rcases hr with ⟨c4, hr1, hr2⟩
      use c4
      specialize ih c4
      constructor
      apply ih
      exact hr1
      exact hr2


theorem addCompPathLen (M : Machine) (c1 c2 c3 : Cfg) (m n : ℕ) :  (∃ c2, (reachN M n c1 c2 ∧ reachN M m c2 c3)) ↔ reachN M (n + m) c1 c3 := by 
  constructor
  intro h
  rcases h with ⟨c, hl, hr⟩
  induction m generalizing c3 with
    | zero =>
      simp
      rw [reachN] at hr
      rw [cfgEquivIffEq] at hr
      rw [← hr]
      exact hl
    | succ m ih =>
      rw [natSucc2, reachN]
      rcases hr with ⟨c4, hr1, hr2⟩
      use c4
      specialize ih c4
      constructor
      apply ih
      exact hr1
      exact hr2
  
  induction n with
    | zero =>
      simp
      intro h
      use c1
      rw [reachN, cfgEquivIffEq]
      constructor
      rfl
      exact h
    | succ n ih => 
      intro h
      rw [natSucc, reachN] at h
      rcases h with ⟨c4, hl, hr⟩
      use c2
      sorry


theorem transFiniteReach (M : Machine) (c1 c2 c3 : Cfg) : (finiteReach M c1 c2 ∧ finiteReach M c2 c3) → (finiteReach M c1 c3) := by
  intro ⟨hl, hr⟩
  rcases hl with ⟨nl, hl⟩
  rcases hr with ⟨nr, hr⟩
  rw [finiteReach]
  use nl+nr
  rw [← addCompPathLen]
  use c2
  exact ⟨hl, hr⟩
  exact c2