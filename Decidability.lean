import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.List
import Mathlib.Data.List.Basic


import TM
import Language


universe u


theorem lCompIff  (L : Language) : ∀ (w : Word),  (w ∈ L ↔ w ∉ Lᶜ) := by
  intro w
  rw [Set.mem_compl_iff]
  simp

--def isDeciderOld (M : Machine) (L : Language) : Prop := 
--  ∀ (w : Word), (
--    (w ∈ L → ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ (isAccept M c2 → finiteReach M c1 c2)) ∧ 
--    (w ∉ L → ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ (isReject M c2 → finiteReach M c1 c2))) 


def isSemiDecider (M : Machine) (L : Language) : Prop := 
  ∀ (w : Word), (w ∈ L → mAcceptsW M w)

def isCoSemiDecider (M : Machine) (L : Language) : Prop := 
  ∀ (w : Word), (w ∉ L → mRejectsW M w)

def isDecider (M : Machine) (L : Language) : Prop := 
  ∀ (w : Word), (w ∈ L → mAcceptsW M w) ∧ (w ∉ L → mRejectsW M w)

def semiDecidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), (w ∈ L → mAcceptsW M w)

def coSemiDecidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), (w ∈ L → mRejectsW M w)

def decidable (L : Language) : Prop := 
  ∃ (M : Machine), ∀ (w : Word), (w ∈ L → mAcceptsW M w) ∧ (w ∉ L → mRejectsW M w)


theorem test {α : Type u} {s : Set α} {x : α} : ¬x ∈ sᶜ ↔ x ∈ s := by
  simp

theorem exDeciderIffDecidable (L : Language) : (∃ (M : Machine), isDecider M L) ↔ decidable L := by
  constructor
  intro ⟨M, h⟩
  use M
  intro w
  specialize h w
  exact h
  intro ⟨M, h⟩
  use M
  intro w
  specialize h w
  exact h

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
  
  

theorem mReachNIffCoMReachN (M : Machine) (c1 c2 : Cfg) (n : ℕ) : reachN M n c1 c2 ↔ reachN (coTm M) n c1 c2 := by
  constructor
  induction n
  intro h
  assumption
  intro h
  rcases h with ⟨c, h⟩
  use c
  constructor
  -- should be by IH ??
  sorry
  rcases h with ⟨h, s, w, d, h1⟩
  use s, w, d
  exact h1
  induction n
  intro h
  assumption
  intro ⟨c, hl, hr⟩
  rcases hr with ⟨s, w, d, h1, h2⟩
  rw [reachN]
  use c
  rw [coTm] at h1
  simp at h1
  constructor
  sorry
  rw [reachSucc]
  use s, w, d
  exact ⟨h1, h2⟩


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

theorem decidableLIffdecidableCoL (L : Language) : decidable L ↔ decidable (Lᶜ) := by
  constructor
  intro ⟨M, h⟩
  rw [decidable]
  use (coTm M)
  intro w
  specialize h w
  rcases h with ⟨hl, hr⟩
  constructor
  simp
  intro wo
  specialize hr wo
  rw [mRejectsWIffCoMAcceptsW] at hr 
  exact hr
  simp
  rw [mAcceptsWIffCoMRejectsW] at hl
  exact hl
  intro ⟨M, h⟩
  rw [decidable]
  use (coTm M)
  intro w
  specialize h w
  rcases h with ⟨hl, hr⟩
  constructor
  simp at hr
  intro wi
  specialize hr wi
  rw [mRejectsWIffCoMAcceptsW] at hr 
  exact hr
  simp
  rw [mAcceptsWIffCoMRejectsW] at hl
  exact hl

theorem langSemiIffCoLangCoSemi (L : Language) : semiDecidable L ↔ coSemiDecidable (Lᶜ) := by
  constructor
  intro ⟨M, h⟩
  rw [coSemiDecidable]
  use (coTm M)
  intro w
  specialize h w
  simp
  rw [mAcceptsW] at h
  rw [mRejectsW]
  repeat sorry


theorem decidableIffLAncCoLDecidable (L : Language) : decidable L ↔ (semiDecidable L ∧ semiDecidable (Lᶜ)) := by
  constructor
  intro ⟨M, h⟩
  constructor
  unfold semiDecidable
  use M
  intro w
  specialize h w
  rcases h with ⟨c1, c2, semi, co_semi⟩
  use c1
  use c2 
  intro wi 
  exact semi wi

  unfold semiDecidable
  use M
  intro w
  specialize h w
  rcases h with ⟨c1, c2, semi, co_semi⟩
  use c1
  use c2
  simp
  intro wo
  sorry
  sorry


theorem decidableIffSemiAndCoSemi (L : Language) : decidable L ↔ (semiDecidable L ∧ coSemiDecidable L) := by
  constructor
  intro ⟨M, h⟩
  constructor
  unfold semiDecidable
  use M
  intro w
  specialize h w
  rcases h with ⟨c1, c2, semi, co_semi⟩
  use c1, c2
  intro wi
  exact semi wi

  unfold coSemiDecidable
  use M
  intro w
  specialize h w
  rcases h with ⟨c1, c2, semi, co_semi⟩
  use c1, c2
  intro wo
  exact co_semi wo

  intro ⟨semi_L, co_semi_L⟩
  rcases semi_L with ⟨M1, semi_L⟩
  specialize semi_L w
  rcases semi_L with ⟨c1, c2, semi_L⟩
  rcases co_semi_L with ⟨M2, co_semi_L⟩
  specialize co_semi_L w
  rcases co_semi_L with ⟨c3, c4, co_semi_L⟩
  rw [decidable]
  use M1 -- construct Machine how ?
  intro w2
  use c1, c2
  -- exact ⟨semi_L, co_semi_L⟩
  sorry
  

  
  

  

  