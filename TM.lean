import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Floor

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


structure TwoCfg where
  state : ℕ
  head : ℕ × ℕ
  left : List (List ℕ)
  right : List (List ℕ)

structure KTapeMachine where
  Q : Finset ℕ
  Λ : Finset ℕ 
  Γ : Finset ℕ 
  F : Finset ℕ
  q0 : ℕ
  k : ℕ
  δ : ℕ × (Fin k → ℕ) → ℕ × (Fin k → ℕ) × (Fin k → Direction)

--def KTapeMachineToMachine (kM : TapeMachine) : Machine :=
--  {Q := kM.Q, Λ := kM.Λ, Γ := kM.Γ ∪ {max kM.Γ+1}, F := kM.F, q0 := kM.q0, δ:=kM.δ}

def logNBaseB (n b : ℕ) : ℕ :=
  (Nat.log2 n) / (Nat.log2 b)

def goedelize (m n : ℕ) : ℕ :=
  2^m*3^n

def deGoedelize (n : ℕ) : ℕ × ℕ :=
  (Nat.floor (logNBaseB n 2), Nat.floor (logNBaseB n 3))

#eval logNBaseB 54 3
#eval goedelize 5 5
#eval (deGoedelize 54)
 
structure ProdMachine where
  Q : Finset (ℕ × ℕ)
  Λ : Finset ℕ 
  Γ : Finset ℕ 
  F : Finset (ℕ × ℕ)
  q0 : ℕ × ℕ
  δ : (ℕ × ℕ) × ℕ → (ℕ × ℕ × Direction) × (ℕ × ℕ × Direction)

def prodMachineFromM1M2 (M1 M2 : Machine) : ProdMachine :=
  {Q := Finset.product M1.Q M2.Q, Λ := M1.Λ ∪ M2.Λ, Γ := M1.Γ ∪ M2.Γ, F := Finset.product (M1.F ∩ M2.F) (M1.F ∩ M2.F) , q0 := (M1.q0, M2.q0),
   δ:= fun (q, γ) => (M1.δ (q.fst, γ), M2.δ (q.snd, γ))}



def prodM (M1 M2 : Machine) : Machine :=
  {Q := (Finset.product M1.Q M2.Q).image (fun n : ℕ × ℕ => 2 ^ n.fst * 3 ^ n.snd), Λ := M1.Λ ∪ M2.Λ, Γ := M1.Γ ∪ M2.Γ,
   F := (Finset.product (M1.F ∪ M2.F) (M1.F ∪ M2.F)).image (fun n : ℕ × ℕ => 2 ^ n.fst * 3 ^ n.snd) , q0 := (2^M1.q0*3^M2.q0),
   δ := fun (q, γ) => (goedelize ((M1.δ ((deGoedelize q).fst, γ)).fst) ((M2.δ ((deGoedelize q).snd, γ)).fst), γ, Direction.N)}


-- q, γ, d

def prodMachineToMachine (pM : ProdMachine) : Machine := 
  {Q := pM.Q.image (fun n : ℕ × ℕ => 2 ^ n.fst * 3 ^ n.snd), Λ := pM.Λ, Γ := pM.Γ, F:= pM.F.image (fun n : ℕ × ℕ => 2 ^ n.fst * 3 ^ n.snd), q0 := 2^pM.q0.fst*2^pM.q0.snd,
   δ := fun (q, γ) => sorry}



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
def updateCfg (cfg: Cfg) (q γ : ℕ) (d: Direction) : Cfg := 
  match cfg.head, d with
    | 0, Direction.L => {state := q, head := 0, left := List.nil,  right := cfg.right.modifyHead γ}
    | _, Direction.L => {state := q, head := cfg.head-1, left := cfg.left.reverse.tail.reverse,  right := [γ].append cfg.left}
    | _, Direction.R => {state := q, head := cfg.head+1, left := cfg.left.append [γ],  right := cfg.right.tail}
    | _, Direction.N => {state := q, head := cfg.head, left := cfg.left,  right := cfg.right.modifyHead γ}

--def reachSuccOld (M : Machine) (c1 c2 : Cfg) : Prop :=
--  ∃ (a γ s w : ℕ) (d : Direction), M.δ (a, γ) = (s, w, d) ∧ cfgEquiv (updateCfg c1 s w d) c2 

def stepMOnC (M : Machine) (c : Cfg) : Cfg :=
  updateCfg c (M.δ (c.state, c.right.head!)).fst (M.δ (c.state, c.right.head!)).snd.fst (M.δ (c.state, c.right.head!)).snd.snd

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


theorem langMNonEmptyIffMAcceptsAnyW (M : Machine) (w : Word) : w ∈ languageOfMachine M ↔ mAcceptsW M w := by
  tauto 

theorem langMNonEmptyIffMAcceptsAnyW2 (M : Machine) : (languageOfMachine M).Nonempty ↔ ∃ (w : Word), mAcceptsW M w := by
  rw [Set.Nonempty]
  tauto

theorem wInLIffWNotInCoL (L : Language) (w : Word) : w ∈ L ↔ w ∉ Lᶜ := by
  simp

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
  
  induction m generalizing c3 with
    | zero =>
      simp
      intro h
      use c3
      rw [reachN, cfgEquivIffEq]
      constructor
      exact h
      rfl
    | succ m ih => 
      intro h
      rw [natSucc2, reachN] at h
      rcases h with ⟨c4, hl, hr⟩
      specialize ih c4
      specialize ih hl
      rcases ih with ⟨c5, ih1, ih2⟩
      use c5
      constructor
      exact ih1
      rw [reachN]
      use c4
      exact ⟨ih2, hr⟩

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


--theorem m1L1AndM2L2EqProdML1AndL2 (M1 M2 : Machine) (L1 L2 : Language) : languageOfMachine M1 ∩ languageOfMachine M2 = languageOfMachine (prodM M1 M2) := by
--  sorry

theorem qMFaIffNotQCoMFa (M : Machine) (c : Cfg) (q : ℕ) : q ∈ M.F ∧ q ∈ M.Q ↔ q ∉ (coTm M).F ∧ q ∈ (coTm M).Q := by
  rw [coTm]
  simp
  intro h
  constructor
  intro h1 _
  exact h1
  intro h3
  apply h3 h

theorem mReachSuccIffCoMReachSucc (M : Machine) (c1 c2 : Cfg) : reachSucc M c1 c2 ↔ reachSucc (coTm M) c1 c2 := by
  constructor
  intro ⟨s, w, d, hl, hr⟩
  use s, w, d
  rw [coTm]
  simp
  have c3 := (updateCfg c1 s w d)
  rw [symCfgEquiv] at hr
  exact ⟨hl, hr⟩ 
  intro ⟨s, w, d, hl, hr⟩
  rw [reachSucc]
  use s, w, d
  exact ⟨hl, hr⟩ 
  
theorem mReachSuccIffCoMreachSucc (M : Machine) (c1 c2 : Cfg) : reachSucc M c1 c2 ↔ reachSucc (coTm M) c1 c2 := by
  constructor
  intro ⟨s, w, d, hl, hr⟩
  use s, w, d
  simp_rw [coTm]
  exact ⟨hl, hr⟩
  intro ⟨s, w, d, hl, hr⟩
  use s, w, d
  simp_rw [coTm]
  exact ⟨hl, hr⟩

theorem mReachNIffCoMReachN (M : Machine) (c1 c2 : Cfg) (n : ℕ) : reachN M n c1 c2 ↔ reachN (coTm M) n c1 c2 := by
  constructor
  induction n generalizing c2 with 
    | zero =>
      intro h
      assumption
    | succ n ih =>
      intro h
      rcases h with ⟨c, hl, hr⟩
      use c
      specialize ih c
      constructor
      apply ih
      exact hl
      rw [← mReachSuccIffCoMReachSucc]
      exact hr
  intro h
  induction n generalizing c2 with 
    | zero =>
      assumption
    | succ n ih =>
      rcases h with ⟨c, hl, hr⟩
      use c
      specialize ih c
      constructor
      apply ih
      exact hl
      rw [mReachSuccIffCoMReachSucc]
      exact hr
      
theorem mFiniteReachIffCoMFiniteReach (M : Machine) (c1 c2 : Cfg) : finiteReach M c1 c2 ↔ finiteReach (coTm M) c1 c2 := by
  rw [finiteReach]
  constructor
  intro ⟨n, h⟩
  
  rw [mReachNIffCoMReachN] at h
  rw [finiteReach]
  use n
  exact h
  intro ⟨n, h⟩
  rw [← mReachNIffCoMReachN] at h
  use n
  exact h

theorem mAcceptsCIffCoMRejectsC (M : Machine) (c : Cfg) : isAccept M c ↔ isReject (coTm M) c := by 
  rw [isAccept, isReject, coTm]
  simp
  intro h
  constructor
  intro h2 _
  exact h2
  intro h4
  apply h4
  exact h

theorem mAcceptsWIffCoMRejectsW (M : Machine) (w : Word) : mAcceptsW M w ↔ mRejectsW (coTm M) w := by 
  rw [mAcceptsW, mRejectsW]
  constructor
  intro ⟨c1, c2, h1, h2, h3, h4⟩
  use c1, c2
  constructor
  exact h1
  constructor  
  rw [mFiniteReachIffCoMFiniteReach] at h2
  exact h2
  rw [isReject, coTm]
  simp
  constructor
  rw [isAccept] at h3
  constructor
  intro _
  exact h3.left
  exact h3.right
  rw [isFinal] at h4
  rw [isFinal]
  simp
  exact h4
  intro ⟨c1, c2, h1, h2, h3⟩
  use c1, c2
  constructor
  exact h1
  constructor
  rw [mFiniteReachIffCoMFiniteReach]
  exact h2
  rw [mAcceptsCIffCoMRejectsC]
  exact h3

theorem mRejectsWIffCoMAcceptsW (M : Machine) (w : Word) : mRejectsW M w ↔ mAcceptsW (coTm M) w := by 
  constructor
  intro h
  rw [mAcceptsWIffCoMRejectsW]
  rw [← mEqCoCoM]
  exact h
  intro h
  rw [mAcceptsWIffCoMRejectsW] at h
  rw [← mEqCoCoM] at h
  exact h


axiom m1OrM2AcceptsWIffProdMAcceptsW (M1 M2 : Machine) (w : Word) : (mAcceptsW M1 w ∨ mAcceptsW M2 w) ↔ mAcceptsW (prodM M1 M2) w

axiom m1AndM2RejectsWIffProdMRejectsW (M1 M2 : Machine) (w : Word) : (mRejectsW M1 w ∨ mRejectsW M2 w) ↔ mRejectsW (prodM M1 M2) w

theorem prodMAcceptsIfM1Accepts (M1 M2 : Machine) (w : Word) : mAcceptsW M1 w → mAcceptsW (prodM M1 M2) w := by
  intro h
  rw [← m1OrM2AcceptsWIffProdMAcceptsW]
  tauto

theorem prodMAcceptsIfM2Accepts (M1 M2 : Machine) (w : Word) : mAcceptsW M2 w → mAcceptsW (prodM M1 M2) w := by
  intro h
  rw [← m1OrM2AcceptsWIffProdMAcceptsW]
  tauto

theorem prodMRejectsIfM1Rejects (M1 M2 : Machine) (w : Word) : mRejectsW M1 w → mRejectsW (prodM M1 M2) w := by
  intro h
  rw [← m1AndM2RejectsWIffProdMRejectsW]
  tauto

theorem prodMRejectsIfM2Rejects (M1 M2 : Machine) (w : Word) : mRejectsW M2 w → mRejectsW (prodM M1 M2) w := by
  intro h
  rw [← m1AndM2RejectsWIffProdMRejectsW]
  tauto

  
axiom wInLAcceptsIffNotWInLRejects (M: Machine) (L : Language) (w : Word) : (w ∈ L ↔ mAcceptsW M w) ↔ (w ∉ L ↔ mRejectsW M w)


theorem wInLAcceptsIffNotWInLRejectsR (M: Machine) (L : Language) (w : Word) : (w ∈ L → mAcceptsW M w) ↔ (w ∉ L → mRejectsW M w) := by
  sorry

theorem coTmAcceptsWNotInLIffMAcceptsWInL (M : Machine) (L : Language) (w : Word) : (¬w ∈ L → mAcceptsW (coTm M) w) ↔ (w ∈ L → mAcceptsW M w) := by
  sorry

theorem wInLMAcceptsIffWNotInLCoMAccepts (M : Machine) (L : Language) (w : Word) : (w ∈ L → mAcceptsW M w) ↔ (w ∉ L → mAcceptsW (coTm M) w) := by
  sorry

theorem mAcceptsWInLIffCoMAcceptsWNotInL (M : Machine) (L : Language) (w : Word) : (mAcceptsW M w → w ∈ L) ↔ (mAcceptsW (coTm M) w → w ∉ L) := by
  sorry

theorem wInLMRejectsIffWNotInLCoMRejects (M : Machine) (L : Language) (w : Word) : (w ∉ L → mRejectsW M w) ↔ (w ∈ L → mRejectsW (coTm M) w) := by
  sorry

theorem mRejectsWInLIffCoMRejectsWNotInL (M : Machine) (L : Language) (w : Word) : (mRejectsW M w → w ∉ L) ↔ (mRejectsW (coTm M) w → w ∈ L) := by
  sorry

theorem wNotInLMRejectsWIffWInLCoMRejectsW (M : Machine) (L : Language) (w : Word) : ¬w ∈ L → mRejectsW M w ↔ w ∈ L → mRejectsW (coTm M) w := by
  sorry