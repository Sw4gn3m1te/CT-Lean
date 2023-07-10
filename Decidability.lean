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
  constructor
  intro wo
  have h2 : ¬ mAcceptsW M w := sorry -- wo at h 
  rw [notMAcceptsWIffMRejectsWOrMHaltsOnW] at h2
  rcases h2 with hl | hr
  exact hl
  sorry -- impossible (but its an or how do i exclude this case ?)
  intro h1
  sorry
  intro ⟨M, h⟩
  rw [semiDecidable]
  use M
  intro w
  specialize h w
  simp at h
  constructor
  intro wo
  have h2 : ¬ mRejectsW M w := sorry -- wo at h
  rw [notMRejectsWIffMAcceptsWOrMHaltsOnW] at h2
  rcases h2 with hl | hr
  exact hl
  sorry -- impossible (but its an or how do i exclude this case ?)
  intro h1
  sorry
  
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
  rcases hl with ⟨hl1, hl2⟩
  rcases hr with ⟨hr1, hr2⟩ 
  constructor
  constructor
  intro wi
  rw [← m1OrM2AcceptsWIffProdMAcceptsW]
  constructor
  exact hl1 wi
  rw [← m1OrM2AcceptsWIffProdMAcceptsW]
  intro h
  rcases h with hl | hr
  exact hl2 hl
  -- coM = coTm M problem
  sorry
  constructor
  intro wo
  rw [← m1AndM2RejectsWIffProdMRejectsW]
  constructor
  sorry
  rw [← m1AndM2RejectsWIffProdMRejectsW]
  intro h
  rcases h with hl | hr
  -- mRejectsW M w = mAcceptsW coM w
  sorry
  sorry


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
  use (prodM M coM)
  intro w
  specialize hl w
  specialize hr w
  constructor
  rw [← m1OrM2AcceptsWIffProdMAcceptsW]
  constructor
  intro wi
  rw [hl] at wi
  left
  exact wi
  intro h
  rcases h with h1 | h2
  rw [hl]
  exact h1
  rw [hl]
  sorry
  sorry
  


theorem wInLAcceptsIffNotWInLRejects (M: Machine) (L : Language) (w : Word) (h : isDecider M L) : (w ∈ L ↔ mAcceptsW M w) ↔ (w ∉ L ↔ mRejectsW M w) := by
  rw [isDecider] at h
  specialize h w
  tauto


theorem wInLOfCoMIffWNotInLOfM (M : Machine) (L : Language) (w : Word) (h : isDecider M L) : w ∈ languageOfMachine (coTm M) ↔ w ∉ languageOfMachine M := by
  rw [isDecider] at h
  specialize h w
  rw [wInLangaugeOfMIffWNotInLanguageOfCoM]
  rw [← mEqCoCoM]
  
theorem coTmAcceptsWNotInLIffMAcceptsWInL (M : Machine) (L : Language) (w : Word) (h : isDecider M L) : (¬w ∈ L → mAcceptsW (coTm M) w) ↔ (w ∈ L → mAcceptsW M w) := by
  rw [← wInLangaugeOfMachineIffMAcceptsW]
  rw [isDecider] at h
  specialize h w
  constructor
  intro _ wi
  rw [h.1] at wi
  exact wi
  intro _ wo
  rw [h.2] at wo
  
  simp
  sorry


theorem wInLMAcceptsIffWNotInLCoMAccepts (M : Machine) (L : Language) (w : Word) (h : L = languageOfMachine M) : (w ∈ L → mAcceptsW M w) ↔ (w ∉ L → mAcceptsW (coTm M) w) := by
  constructor
  intro _ wo
  rw [h] at wo
  rw [mRejectsWNotInLanguageOfMachine] at wo
  rw [← mRejectsWIffCoMAcceptsW]
  sorry
  intro _ wi
  rw [h] at wi
  rw [← wInLangaugeOfMachineIffMAcceptsW]
  exact wi

theorem mAcceptsWInLIffCoMAcceptsWNotInL (M : Machine) (L : Language) (w : Word) (h : L = languageOfMachine M) : (mAcceptsW M w → w ∈ L) ↔ (mAcceptsW (coTm M) w → w ∉ L) := by
  constructor
  intro _ wo
  rw [h]
  rw [mRejectsWNotInLanguageOfMachine]
  rw [← mRejectsWIffCoMAcceptsW] at wo
  sorry
  intro _ wi
  rw [h]
  rw [← wInLangaugeOfMachineIffMAcceptsW] at wi
  exact wi

theorem wInLMRejectsIffWNotInLCoMRejects (M : Machine) (L : Language) (w : Word) (h : L = languageOfMachine M) : (w ∉ L → mRejectsW M w) ↔ (w ∈ L → mRejectsW (coTm M) w) := by
  constructor
  intro _ wo
  rw [h] at wo
  rw [mRejectsWIffCoMAcceptsW]
  rw [← mEqCoCoM]
  rw [← wInLangaugeOfMachineIffMAcceptsW]
  exact wo
  intro _ wi
  rw [h] at wi
  sorry
  --rw [← mRejectsWNotInLanguageOfMachine]
  --exact wi


theorem mRejectsWInLIffCoMRejectsWNotInL (M : Machine) (L : Language) (w : Word) (h : L = languageOfMachine M) : (mRejectsW M w → w ∉ L) ↔ (mRejectsW (coTm M) w → w ∈ L) := by
  constructor
  intro _ wo
  rw [h]
  rw [← mAcceptsWIffCoMRejectsW] at wo
  rw [wInLangaugeOfMachineIffMAcceptsW]
  exact wo
  intro _ wi
  rw [h]
  rw [mRejectsWNotInLanguageOfMachine]
  sorry
