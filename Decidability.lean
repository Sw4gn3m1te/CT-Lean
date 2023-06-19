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

def isSemiDecider (M : Machine) (L : Language) : Prop := 
  ∀ (w : Word), (w ∈ L ↔ mAcceptsW M w)

def isCoSemiDecider (M : Machine) (L : Language) : Prop := 
  ∀ (w : Word), (w ∉ L ↔ mRejectsW M w)

def isDecider (M : Machine) (L : Language) : Prop := 
  ∀ (w : Word), (w ∈ L ↔ mAcceptsW M w) ∧ (w ∉ L ↔ mRejectsW M w)

def semiDecidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), (w ∈ L ↔ mAcceptsW M w)

def coSemiDecidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), (w ∈ L ↔ mRejectsW M w)

-- use iff ?
def decidable (L : Language) : Prop := 
  ∃ (M : Machine), ∀ (w : Word), (w ∈ L ↔ mAcceptsW M w) ∧ (w ∉ L ↔ mRejectsW M w)


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
  rw [← mRejectsWIffCoMAcceptsW]
  exact hr
  simp
  rw [← mAcceptsWIffCoMRejectsW]
  exact hl
  intro ⟨M, h⟩
  rw [decidable]
  use (coTm M)
  intro w
  specialize h w
  rcases h with ⟨hl, hr⟩
  constructor
  simp at hr
  rw [← mRejectsWIffCoMAcceptsW]
  exact hr
  simp at hl
  rw [← mAcceptsWIffCoMRejectsW]
  exact hl


theorem langSemiIffCoLangCoSemi (L : Language) : semiDecidable L ↔ coSemiDecidable (Lᶜ) := by
  constructor
  intro ⟨M, h⟩
  rw [coSemiDecidable]
  use M
  intro w
  specialize h w
  simp
  rcases h with ⟨hl ,hr⟩
  constructor
  intro wo
  rw [wInLMAcceptsIffWNotInLCoMAccepts] at hl
  rw [← mRejectsWIffCoMAcceptsW] at hl
  exact hl wo
  intro h
  rw [mAcceptsWInLIffCoMAcceptsWNotInL] at hr
  rw [← mRejectsWIffCoMAcceptsW] at hr
  exact hr h
  intro ⟨M, h⟩
  rw [semiDecidable]
  use M
  intro w
  specialize h w
  simp at h
  rcases h with ⟨hl ,hr⟩
  constructor
  intro wo
  rw [wNotInLMRejectsWIffWInLCoMRejectsW] at hl
  rw [mAcceptsWIffCoMRejectsW]
  exact hl wo
  intro h
  rw [mRejectsWInLIffCoMRejectsWNotInL] at hr
  rw [mAcceptsWIffCoMRejectsW] at h
  exact hr h
  
theorem decidableIffLAncCoLDecidable (L : Language) : decidable L ↔ (semiDecidable L ∧ semiDecidable (Lᶜ)) := by
  constructor
  intro ⟨M, h⟩
  constructor
  rw [semiDecidable]
  use M
  intro w
  specialize h w
  rcases h with ⟨hl, hr⟩
  exact hl
  rw [semiDecidable]
  use (coTm M)
  intro w
  specialize h w
  simp
  rcases h with ⟨hl, hr⟩
  rw [mAcceptsWIffCoMRejectsW]
  rw [← mEqCoCoM]
  exact hr
  intro ⟨hl, hr⟩
  rw [decidable]
  rcases hl with ⟨M, hl⟩
  rcases hr with ⟨coM, hr⟩
  use (prodM M coM)
  intro w
  specialize hl w
  specialize hr w
  constructor
  repeat sorry


theorem decidableIffSemiAndCoSemi (L : Language) : decidable L ↔ (semiDecidable L ∧ coSemiDecidable L) := by
  constructor
  intro ⟨M, h⟩
  constructor
  rw [semiDecidable]
  use M
  intro w
  specialize h w
  rcases h with ⟨hl, hr⟩ 
  exact hl
  rw [coSemiDecidable]
  use (coTm M)
  intro w
  specialize h w
  rcases h with ⟨hl, hr⟩ 
  rw [← mAcceptsWIffCoMRejectsW]
  exact hl
  intro ⟨hl, hr⟩
  rcases hl with ⟨M, hl⟩
  rcases hr with ⟨coM, hr⟩
  use M
  intro w
  specialize hl w
  specialize hr w
  constructor
  exact hl
  sorry





  
  

  

  