import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.LibrarySearch

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
  -- Q × Γ → Q × Γ × Direction
  δ : ℕ × ℕ → ℕ × ℕ × Direction

  FInQ:
    F ⊆ Q
  

structure Dtm extends Machine where

  uniqueness:
    ∀ x y, (δ x = δ y ↔ x = y)


def startCfg (M : Dtm) (w : Word) : Cfg := 
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
  ((Float.log2 n.toFloat) / (Float.log2 b.toFloat)).toUInt64.toNat

def goedelize (m n : ℕ) : ℕ :=
  2^m*3^n

def deGoedelize (n : ℕ) : ℕ × ℕ := 
  (List.count 2 (Nat.factors n), List.count 3 (Nat.factors n))

#eval goedelize 5 12
#eval (deGoedelize (goedelize 5 12))

theorem goedelizePreservesSize (A : Finset ℕ) : (Finset.product A A).card = ((Finset.product A A).image (fun n : ℕ × ℕ => goedelize n.fst n.snd)).card := by
  sorry

theorem goedelProductPreservesSubset (A B : Finset ℕ) (h0 : A ⊆ B) : Finset.product A A ⊆ Finset.product B B ↔ (Finset.product A A).image (fun n : ℕ × ℕ => goedelize n.fst n.snd) ⊆ (Finset.product B B).image (fun n : ℕ × ℕ => goedelize n.fst n.snd) := by
  sorry


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


def prodM (M1 M2 : Dtm) : Dtm :=
  {Q := (Finset.product M1.Q M2.Q).image (fun n : ℕ × ℕ => goedelize n.fst n.snd), Λ := M1.Λ ∪ M2.Λ, Γ := M1.Γ ∪ M2.Γ,
   F := (Finset.product M1.F M2.F).image (fun n : ℕ × ℕ => goedelize n.fst n.snd) , q0 := goedelize M1.q0 M2.q0,
   δ := fun (q, γ) => (goedelize ((M1.δ ((deGoedelize q).fst, γ)).fst) ((M2.δ ((deGoedelize q).snd, γ)).fst), γ, Direction.N),
   FInQ := by sorry, uniqueness := by sorry}


def coTm (M : Dtm) : Dtm :=
  {Q:=M.Q, Λ:=M.Λ, Γ:=M.Γ, F:=(M.Q \ M.F), q0:=M.q0, δ:=M.δ, FInQ := by simp, uniqueness := M.uniqueness}


theorem mEqCoCoM (M : Dtm) : M = coTm (coTm M) := by
  repeat rw [coTm]
  dsimp
  simp
  obtain ⟨Q, uniqueness⟩ := M
  simp
  obtain ⟨Q, Λ2, Γ, F, q0, δ, fInQ⟩ := Q
  simp
  ext q
  simp
  tauto

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
    | _, Direction.L => {state := q, head := cfg.head-1, left := cfg.left.reverse.tail.reverse,  right := [cfg.left.reverse.head!, γ].append cfg.right.tail}
    | _, Direction.R => {state := q, head := cfg.head+1, left := cfg.left.append [γ],  right := cfg.right.tail}
    | _, Direction.N => {state := q, head := cfg.head, left := cfg.left,  right := cfg.right.modifyHead γ}

--def reachSuccOld (M : Machine) (c1 c2 : Cfg) : Prop :=
--  ∃ (a γ s w : ℕ) (d : Direction), M.δ (a, γ) = (s, w, d) ∧ cfgEquiv (updateCfg c1 s w d) c2 

def stepMOnC (M : Dtm) (c : Cfg) : Cfg :=
  updateCfg c (M.δ (c.state, c.right.head!)).fst (M.δ (c.state, c.right.head!)).snd.fst (M.δ (c.state, c.right.head!)).snd.snd


def reachSucc (M : Dtm) (c1 c2 : Cfg) : Prop :=
  ∃ (s w : ℕ) (d : Direction), M.δ (c1.state, c1.right.head!) = (s, w, d) ∧ cfgEquiv (updateCfg c1 s w d) c2 

def isAccept (M : Dtm) (cfg : Cfg)  : Prop :=
  cfg.state ∈ M.F ∧ cfg.state ∈ M.Q

def isReject (M : Dtm) (cfg : Cfg)  : Prop :=
  cfg.state ∉ M.F ∧ cfg.state ∈ M.Q

-- just stand still if term ?
def isFinal (M  : Dtm) (cfg : Cfg) : Prop :=
  M.δ (cfg.state, cfg.right.head!) = (cfg.state, cfg.right.head!, Direction.N) ∧ cfg.state ∈ M.Q


def reachN (M : Dtm) (n : ℕ) (c1 c2 : Cfg) : Prop :=
  match n with
  | 0 => cfgEquiv c1 c2
  | Nat.succ m => ∃ (c : Cfg), (reachN M m c1 c ∧ reachSucc M c c2)

def finiteReach (M : Dtm) (c1 c2 : Cfg) : Prop :=
  ∃ (n : ℕ), reachN M n c1 c2

def mHaltsOnW (M : Dtm) (w : Word) : Prop :=
  ∃ (c : Cfg), finiteReach M (startCfg M w) c ∧ isFinal M c

def mAcceptsW (M : Dtm) (w : Word) : Prop :=
  ∃ (c : Cfg), finiteReach M (startCfg M w) c ∧ isAccept M c ∧ isFinal M c

def mRejectsW (M : Dtm) (w : Word) : Prop :=
 ¬ mAcceptsW M w ∧ mHaltsOnW M w
 -- ∀ (c:Cfg), (isFinal M c ∧ finiteReach M (startCfg M w) ∧ ) c → isReject M c 

 
def languageOfMachine (M : Dtm) : Language := 
  { w | mAcceptsW M w}


theorem startCfgTmEqstartCfgCoTm (M : Dtm) : startCfg M = startCfg (coTm M) := by
  tauto

theorem isFinalMIffisFinalcoTm (M : Dtm) (c : Cfg) : isFinal M c ↔ isFinal (coTm M) c := by
  tauto

theorem noHaltingMachineExists (MHalt M : Dtm) (w : Word) : ¬ ∃ (MHalt : Dtm), (∀ M, mHaltsOnW M w) := by
  sorry


theorem langMNonEmptyIffMAcceptsAnyW (M : Dtm) : (languageOfMachine M).Nonempty ↔ ∃ (w : Word), mAcceptsW M w := by
  rw [Set.Nonempty]
  tauto

theorem wInLIffWNotInCoL (L : Language) (w : Word) : w ∈ L ↔ w ∉ Lᶜ := by
  simp


-- if c2 can be reached from c1 then there ex a sequence cs of configs from c1 to c2 (maybe emtpy if c2 is succ of c1)
theorem pathReachability (M : Dtm) (c1 c2 : Cfg) : finiteReach M c1 c2 → (∃ (cs : List Cfg), ∀ (c : Cfg), c ∈ cs → finiteReach M c c2) := by
  sorry
  

theorem reach2IfReachSuccSucc (M : Dtm) (c1 c2 c3 : Cfg) : reachSucc M c1 c2 ∧ reachSucc M c2 c3 → reachN M 2 c1 c3 := by
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

theorem finiteReachIffReachN (c1 c2 : Cfg) (M : Dtm) : finiteReach M c1 c2 ↔ ∃ (n : ℕ), reachN M n c1 c2 := by
  constructor
  intro ⟨n , h⟩
  use n
  exact h
  intro ⟨n ,h⟩
  rw [finiteReach]
  use n
  exact h
  

theorem reach0EqCfgEquiv (M : Dtm) (c1 c2 : Cfg) : reachN M 0 c1 c2 ↔ cfgEquiv c1 c2 := by
  constructor
  rw [reachN]
  simp
  rw [reachN]
  simp

theorem reachNPlusOne (M : Dtm) (c1 c3 : Cfg) (n : ℕ) : (∃ (c : Cfg), (reachN M n c1 c ∧ reachSucc M c c3)) ↔ reachN M (Nat.succ n) c1 c3 := by
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


theorem addCompPathLen2 (M : Dtm) (c1 c2 c3 : Cfg) (m n : ℕ) :  (∃ c2, (reachN M m c1 c2 ∧ reachN M n c2 c3)) → reachN M (m + n) c1 c3 := by 
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


theorem addCompPathLen (M : Dtm) (c1 c2 c3 : Cfg) (m n : ℕ) :  (∃ c2, (reachN M n c1 c2 ∧ reachN M m c2 c3)) ↔ reachN M (n + m) c1 c3 := by 
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

theorem transFiniteReach (M : Dtm) (c1 c2 c3 : Cfg) : (finiteReach M c1 c2 ∧ finiteReach M c2 c3) → (finiteReach M c1 c3) := by
  intro ⟨hl, hr⟩
  rcases hl with ⟨nl, hl⟩
  rcases hr with ⟨nr, hr⟩
  rw [finiteReach]
  use nl+nr
  rw [← addCompPathLen]
  use c2
  exact ⟨hl, hr⟩
  exact c2


theorem qMFIffNotQCoMF (M : Dtm) (q : ℕ) : q ∈ M.F ∧ q ∈ M.Q ↔ q ∉ (coTm M).F ∧ q ∈ (coTm M).Q := by
  rw [coTm]
  simp
  intro h
  constructor
  intro h1 _
  exact h1
  intro h3
  apply h3 h

theorem mReachSuccIffCoMReachSucc (M : Dtm) (c1 c2 : Cfg) : reachSucc M c1 c2 ↔ reachSucc (coTm M) c1 c2 := by
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
  
theorem mReachSuccIffCoMreachSucc (M : Dtm) (c1 c2 : Cfg) : reachSucc M c1 c2 ↔ reachSucc (coTm M) c1 c2 := by
  constructor
  intro ⟨s, w, d, hl, hr⟩
  use s, w, d
  simp_rw [coTm]
  exact ⟨hl, hr⟩
  intro ⟨s, w, d, hl, hr⟩
  use s, w, d
  simp_rw [coTm]
  exact ⟨hl, hr⟩

theorem mReachNIffCoMReachN (M : Dtm) (c1 c2 : Cfg) (n : ℕ) : reachN M n c1 c2 ↔ reachN (coTm M) n c1 c2 := by
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
      
theorem mFiniteReachIffCoMFiniteReach (M : Dtm) (c1 c2 : Cfg) : finiteReach M c1 c2 ↔ finiteReach (coTm M) c1 c2 := by
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

theorem mAcceptsCIffCoMRejectsC (M : Dtm) (c : Cfg) : isAccept M c ↔ isReject (coTm M) c := by
  rw [isAccept, isReject, coTm]
  simp
  intro h
  constructor
  intro h2 _
  exact h2
  intro h4
  apply h4
  exact h


theorem isAcceptIffIsNotReject (M : Dtm) (c : Cfg) (h0 : c.state ∈ M.Q)  : isAccept M c ↔ ¬ isReject M c := by
  constructor
  intro h
  rw [isReject]
  simp
  rw [isAccept] at h
  tauto
  intro h
  rw [isAccept]
  simp
  rw [isReject] at h
  tauto

theorem isRejectIfIsNotAccept (M : Dtm) (c : Cfg) (h0 : c.state ∈ M.Q) : ¬ isAccept M c → isReject M c := by
  rw [isAcceptIffIsNotReject]
  simp
  exact h0

theorem mAccpetsWAndMRejectsWIffFalse (M : Dtm) (w : Word) : mAcceptsW M w ∧ mRejectsW M w ↔ False := by
  constructor
  intro ⟨h1, h2⟩
  rcases h2 with ⟨hl, _⟩
  exact hl h1
  tauto


theorem prodMAcceptsWIffM1OrM2AccpetsW (M1 M2 : Dtm) (w : Word) : mAcceptsW (prodM M1 M2) w ↔ (mAcceptsW M1 w) := by
  sorry

theorem prodMRejectsWIffM1AndM2RejectsW (M1 M2 : Dtm) (w : Word) : mRejectsW (prodM M1 M2) w ↔ (mAcceptsW M2 w) := by
  sorry

theorem prodMHaltsOnWIffM1OrM2HaltsOnW (M1 M2 : Dtm) (w : Word) : mHaltsOnW (prodM M1 M2) w := by
  sorry

theorem mHaltsOnWIffMAcceptsWOrMRejectsW (M : Dtm) (w : Word) : mHaltsOnW M w ↔ (mAcceptsW M w ∨ mRejectsW M w) := by
  constructor
  intro h
  rcases h with ⟨c, h1, h2⟩
  have g : w ∈ languageOfMachine M ∨ w ∉ languageOfMachine M := by tauto
  rcases g with gi | go
  left
  tauto
  right
  rw [languageOfMachine] at go
  simp at go
  constructor
  exact go
  rw [mHaltsOnW]
  use c
  exact ⟨h1, h2⟩
  intro h
  rcases h with ⟨c1, hl1, _, hl3⟩ | ⟨_, c2, hr2, hr3⟩
  rw [mHaltsOnW]
  use c1
  exact ⟨hl1, hl3⟩
  rw [mHaltsOnW]
  use c2
  exact ⟨hr2, hr3⟩

theorem notMHaltsOnWIffNotMAcceptsWAndNotMRejectsW (M : Dtm) (w : Word) : ¬ mHaltsOnW M w ↔ (¬ mRejectsW M w ∧ ¬ mAcceptsW M w) := by
  rw [mHaltsOnWIffMAcceptsWOrMRejectsW]
  tauto

theorem mAcceptsWIffNotMRejectsWAndMHaltsOnW (M : Dtm) (w : Word) : mAcceptsW M w ↔ ¬ mRejectsW M w ∧ mHaltsOnW M w := by
  constructor
  intro h
  constructor
  by_contra f
  have g : mAcceptsW M w ∧ mRejectsW M w := ⟨h, f⟩
  rw [mAccpetsWAndMRejectsWIffFalse] at g
  exact g
  rw [mHaltsOnWIffMAcceptsWOrMRejectsW]
  left
  exact h
  rintro ⟨hl, hr⟩
  rw [mHaltsOnWIffMAcceptsWOrMRejectsW] at hr
  rcases hr with hr1 | hr2
  exact hr1
  by_contra _
  exact hl hr2

theorem notMAcceptsWAndNotMRejectsWIffNotMHaltsOnW (M : Dtm) (w : Word) : (¬ mAcceptsW M w ∧ ¬ mRejectsW M w) ↔ ¬ mHaltsOnW M w := by
  constructor
  rintro ⟨hl, hr⟩
  by_contra f
  rw [mHaltsOnWIffMAcceptsWOrMRejectsW] at f
  rcases f with f1 | f2
  exact hl f1
  exact hr f2
  rw [mAcceptsW, mHaltsOnW, mRejectsW]
  simp
  intro h
  constructor
  intro c h1 _ h2
  specialize h c
  have f := h h1
  exact f h2
  rw [mHaltsOnW, mAcceptsW]
  simp
  intro _
  intro c
  specialize h c
  exact h

theorem notMAcceptsWIffMRejectsWOrMHaltsOnW (M : Dtm) (w : Word) : ¬ mAcceptsW M w ↔ (mRejectsW M w ∨ ¬ mHaltsOnW M w) := by
  constructor
  intro h
  by_contra f
  push_neg at f
  rcases f with ⟨f1, f2⟩
  have f3 : ¬mAcceptsW M w ∧ ¬mRejectsW M w := ⟨h, f1⟩
  rw [notMAcceptsWAndNotMRejectsWIffNotMHaltsOnW] at f3
  exact f3 f2
  intro h
  rcases h with hl | hr
  by_contra f
  rw [mAcceptsWIffNotMRejectsWAndMHaltsOnW] at f
  exact f.1 hl
  by_contra f
  rw [notMHaltsOnWIffNotMAcceptsWAndNotMRejectsW] at hr
  exact hr.2 f

theorem mRejectsWIffNotMAcceptsWAndMHaltsOnW (M : Dtm) (w : Word) : mRejectsW M w ↔ (¬ mAcceptsW M w ∧ mHaltsOnW M w) := by
  constructor
  intro h
  rw [notMAcceptsWIffMRejectsWOrMHaltsOnW]
  constructor
  left
  exact h
  rw [mHaltsOnWIffMAcceptsWOrMRejectsW]
  right
  exact h
  rintro ⟨hl, hr⟩
  by_contra f
  rw [notMAcceptsWIffMRejectsWOrMHaltsOnW] at hl
  rcases hl with hl1 | hl2
  exact f hl1
  exact hl2 hr 

theorem notMRejectsWIffMAcceptsWOrMHaltsOnW (M : Dtm) (w : Word) : ¬ mRejectsW M w ↔ (mAcceptsW M w ∨ ¬ mHaltsOnW M w) := by
  constructor
  intro h
  by_contra f
  push_neg at f
  rcases f with ⟨f1, f2⟩
  have f3 : ¬ mHaltsOnW M w
  have g := notMAcceptsWAndNotMRejectsWIffNotMHaltsOnW M w
  rw [← g]
  exact ⟨f1, h⟩
  exact f3 f2
  intro h
  rcases h with hl | hr
  by_contra f
  rw [mRejectsWIffNotMAcceptsWAndMHaltsOnW] at f
  exact f.1 hl
  by_contra f
  rw [notMHaltsOnWIffNotMAcceptsWAndNotMRejectsW] at hr
  exact hr.1 f


theorem wInLangaugeOfMachineIffMAcceptsW (M : Dtm) (w : Word) : w ∈ languageOfMachine M ↔ mAcceptsW M w := by
  tauto 

theorem wNotInLanguageOfMachineIffNotMAcceptsW (M : Dtm) (w : Word) : w ∉ languageOfMachine M ↔ ¬ mAcceptsW M w := by
  tauto

theorem wNotInLanguageOfMachineIfMRejectesW (M : Dtm) (w : Word) : mRejectsW M w → w ∉ languageOfMachine M := by
  intro h
  rw [wNotInLanguageOfMachineIffNotMAcceptsW]
  rw [mRejectsWIffNotMAcceptsWAndMHaltsOnW] at h
  exact h.1

theorem mHaltsOnWIfMAcceptsW (M : Dtm) (w : Word) : mAcceptsW M w → mHaltsOnW M w := by
  rw [mAcceptsW]
  rintro ⟨c, h⟩
  use c
  exact ⟨h.1, h.2.2⟩

theorem mHaltsOnWIfMRejectsW (M : Dtm) (w : Word) : mRejectsW M w → mHaltsOnW M w := by
  intro ⟨_, h⟩
  exact h


theorem mHaltsOrMNotHalts (M : Dtm) (w : Word) : mHaltsOnW M w ∨ ¬ mHaltsOnW M w := by
  tauto

  -- R ∨ ¬ H →neg (A ∨ ¬ H) ∧ H = A ∧ H (cont. with h)
theorem mRejectsWNotInLanguageOfMachine (M : Dtm) (w : Word) : w ∉ languageOfMachine M ↔ (mRejectsW M w ∨ ¬ mHaltsOnW M w) := by 
  constructor
  intro h
  by_contra f
  push_neg at f
  rcases f with ⟨f1, f2⟩
  rw [notMRejectsWIffMAcceptsWOrMHaltsOnW] at f1
  have g : (mAcceptsW M w ∨ ¬mHaltsOnW M w) ∧ mHaltsOnW M w := ⟨f1, f2⟩ 
  have g2 : mAcceptsW M w  ∧ mHaltsOnW M w
  constructor
  rcases f1 with fl | fr
  exact fl
  contradiction
  exact f2
  rw [wNotInLanguageOfMachineIffNotMAcceptsW] at h
  exact h g2.1
  intro h
  by_contra f
  rw [wInLangaugeOfMachineIffMAcceptsW] at f
  rcases h with hl | hr
  rw [mRejectsWIffNotMAcceptsWAndMHaltsOnW] at hl
  exact hl.1 f
  rw [mAcceptsWIffNotMRejectsWAndMHaltsOnW] at f
  exact hr f.2


theorem mHaltsOnWIffCoMHaltsOnW (M : Dtm) (w : Word) : mHaltsOnW M w ↔ mHaltsOnW (coTm M) w := by
  constructor
  intro h
  rw [mHaltsOnW]
  rcases h with ⟨c, h⟩
  use c
  rw [← mFiniteReachIffCoMFiniteReach, ← startCfgTmEqstartCfgCoTm, ← isFinalMIffisFinalcoTm]
  exact h
  intro h
  rcases h with ⟨c, h⟩
  use c
  rw [mFiniteReachIffCoMFiniteReach, startCfgTmEqstartCfgCoTm, isFinalMIffisFinalcoTm]
  exact h

theorem mAcceptsWAndCoMAcceptsWIffFalse (M : Dtm) (w : Word) : (mAcceptsW M w ∧ mAcceptsW (coTm M) w) ↔ False := by
  constructor
  intro ⟨hl, hr⟩
  rcases hl with ⟨c1, hl⟩
  rcases hr with ⟨c2, hr⟩
  have f : c1 = c2 := sorry -- by uniqueness
  have g1 := hl.2.1
  have g2 := hr.2.1
  rw [← f] at g2
  rw [mAcceptsCIffCoMRejectsC] at g1
  rw [isAccept] at g2
  rw [isReject] at g1
  exact g1.1 g2.1
  simp

theorem mRejectsWAndCoMRejectsWIffFalse (M : Dtm) (w : Word) : (mRejectsW M w ∧ mRejectsW (coTm M) w) ↔ False := by
  constructor
  repeat rw [mRejectsW, mAcceptsW]
  intro ⟨h1, h2, c, h3⟩
  rcases h1 with ⟨h1, h4⟩
  simp at h1 h2
  specialize h1 c
  specialize h2 c
  rw [← mFiniteReachIffCoMFiniteReach, ← startCfgTmEqstartCfgCoTm] at h2
  rw [mAcceptsCIffCoMRejectsC, ← mEqCoCoM, ← isFinalMIffisFinalcoTm] at h2
  rw [← isFinalMIffisFinalcoTm, ← startCfgTmEqstartCfgCoTm, ← mFiniteReachIffCoMFiniteReach] at h3
  have g1 := h1 h3.1
  have g2 := h2 h3.1
  have g3 : isAccept M c ∨ isReject M c
  by_contra f
  push_neg at f
  rw [← isAcceptIffIsNotReject] at f
  tauto
  rw [isFinal] at h3
  exact h3.2.2
  rcases g3 with ga | gr
  have g3 := g1 ga
  exact g3 h3.2
  have g3 := g2 gr
  exact g3 h3.2
  tauto

-- M and CoM take the same path hence land in the same end config

theorem mAcceptsWIffCoMRejectsW (M : Dtm) (w : Word) : mAcceptsW M w ↔ mRejectsW (coTm M) w := by
  constructor
  intro h
  rw [mRejectsW]
  constructor
  by_contra f
  have g : mAcceptsW M w ∧ mAcceptsW (coTm M) w := ⟨h, f⟩
  rw [mAcceptsWAndCoMAcceptsWIffFalse] at g
  exact g
  rw [← mHaltsOnWIffCoMHaltsOnW]
  apply mHaltsOnWIfMAcceptsW M w
  exact h
  intro h
  rcases h with ⟨h1, h2⟩
  rw [notMAcceptsWIffMRejectsWOrMHaltsOnW] at h1
  rcases h1 with h1 | h2
  by_contra f
  rw [notMAcceptsWIffMRejectsWOrMHaltsOnW] at f
  rcases f with f1 | f2
  have g : mRejectsW M w ∧ mRejectsW (coTm M) w := ⟨f1, h1⟩
  rw [mRejectsWAndCoMRejectsWIffFalse] at g
  exact g
  rw [mHaltsOnWIffCoMHaltsOnW] at f2
  repeat contradiction

theorem mRejectsWIffCoMAcceptsW (M : Dtm) (w : Word) : mRejectsW M w ↔ mAcceptsW (coTm M) w := by 
  constructor
  intro h
  rw [mAcceptsWIffCoMRejectsW]
  rw [← mEqCoCoM]
  exact h
  intro h
  rw [mAcceptsWIffCoMRejectsW] at h
  rw [← mEqCoCoM] at h
  exact h
