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
  -- ∃ (M : Machine), ∀ (w : Word), (w ∈ L ↔ mRejectsW M w)
  -- semiDecidable Lᶜ 
  ∃ (M : Machine), ∀ (w : Word), (w ∉ L ↔ mAcceptsW M w)

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
  exact h
  intro ⟨M, h⟩
  use M
  intro w
  specialize h w
  simp at h
  exact h

theorem langCoSemiIffCoLangSemi (L : Language) : coSemiDecidable L ↔ semiDecidable (Lᶜ) := by
  rw [langSemiIffCoLangCoSemi]
  simp


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
  rw [← mRejectsWIffCoMAcceptsW]
  exact hr
  intro ⟨hl, hr⟩
  rcases hl with ⟨M, hl⟩
  rcases hr with ⟨coM, hr⟩
  use (prodM M coM)
  intro w
  specialize hl w
  specialize hr w
  constructor
  rw [prodMAcceptsWIffM1OrM2AccpetsW]
  constructor
  intro wi
  rw [hl] at wi
  left
  exact wi
  have g1 : w ∉ L ↔ mRejectsW M w ∨ ¬ mHaltsOnW M w := sorry
  have g2 : w ∉ L ↔ mAcceptsW coM w ∨ ¬ mHaltsOnW coM w := sorry
  intro h
  rcases h with h1 | h2
  rw [hl]
  exact h1

  sorry
  sorry


theorem decidableIffLAncCoLDecidable (L : Language) : decidable L ↔ (semiDecidable L ∧ semiDecidable (Lᶜ)) := by
  rw [← langCoSemiIffCoLangSemi]
  rw [← decidableIffSemiAndCoSemi]

theorem winLIffMAcceptsWOrCoMRejectsW (M : Machine) (L : Language) (w : Word) (h : isDecider M L) : w ∈ L ↔ mAcceptsW M w ∨ mRejectsW (coTm M) w := by
  rw [isDecider] at h
  specialize h w
  constructor 
  intro wi
  left
  rw [h.1] at wi
  exact wi
  intro h2
  rcases h2 with hl | hr
  rw [← h.1] at hl 
  exact hl
  rw [← mAcceptsWIffCoMRejectsW] at hr
  rw [← h.1] at hr
  exact hr

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
  rw [wInLangaugeOfMachineIffMAcceptsW]
  rw [← mRejectsWIffCoMAcceptsW]
  exact wo

theorem wInLMAcceptsIffWNotInLCoMAccepts (M : Machine) (L : Language) (w : Word) (h : isDecider M L) : (w ∈ L → mAcceptsW M w) ↔ (w ∉ L → mAcceptsW (coTm M) w) := by
  rw [isDecider] at h
  specialize h w
  constructor
  intro _ wo
  rw [← mRejectsWIffCoMAcceptsW]
  rw [h.2] at wo
  exact wo
  intro _ wi
  rw [h.1] at wi
  exact wi

theorem mAcceptsWInLIffCoMAcceptsWNotInL (M : Machine) (L : Language) (w : Word) (h : isDecider M L) : (mAcceptsW M w → w ∈ L) ↔ (mAcceptsW (coTm M) w → w ∉ L) := by
  rw [isDecider] at h
  specialize h w
  constructor
  intro _ wo
  rw [← mRejectsWIffCoMAcceptsW] at wo
  rw [← h.2] at wo
  exact wo
  intro _ wi
  rw [← h.1] at wi
  exact wi

theorem wInLMRejectsIffWNotInLCoMRejects (M : Machine) (L : Language) (w : Word) (h : isDecider M L) : (w ∉ L → mRejectsW M w) ↔ (w ∈ L → mRejectsW (coTm M) w) := by
  rw [isDecider] at h
  specialize h w
  constructor
  intro _ wi
  rw [h.1] at wi
  rw [← mAcceptsWIffCoMRejectsW]
  exact wi
  intro _ wo
  rw [h.2] at wo
  exact wo


theorem mRejectsWInLIffCoMRejectsWNotInL (M : Machine) (L : Language) (w : Word) (h : isDecider M L) : (mRejectsW M w → w ∉ L) ↔ (mRejectsW (coTm M) w → w ∈ L) := by
  rw [isDecider] at h
  specialize h w
  constructor
  intro _ wi
  rw [h.1]
  rw [← mAcceptsWIffCoMRejectsW] at wi
  exact wi
  intro _ wo
  rw [h.2]
  exact wo

