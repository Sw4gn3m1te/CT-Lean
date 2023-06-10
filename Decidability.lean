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


def isDecider (M : Machine) : Prop := 
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil, right := w} ∧
    ((isAccept M c2 ∨ isReject M c2) → finiteReach M c1 c2)

def isEnumerator (M : Machine) (L : Language) : Prop :=
  ∀ (w : Word), w ∈ L → ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ 
    (isAccept M c2 → finiteReach M c1 c2)

def isSemiDecider (M : Machine) : Prop :=
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ 
    (isAccept M c2 → finiteReach M c1 c2)

def isCoSemiDecider (M : Machine) : Prop :=
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ 
    (isReject M c2 → finiteReach M c1 c2)

def semiDecidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg),
    (w ∈ L → c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ finiteReach M c1 c2 ∧ isAccept M c2)

def coSemiDecidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg),
    (w ∉ L → c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ finiteReach M c1 c2 ∧ isReject M c2)

def decidable (L : Language) : Prop := 
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg), 
    ((w ∈ L → c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ finiteReach M c1 c2 ∧ isAccept M c2) ∧ 
    (w ∉ L → c1 = {state := 0, head := 0, left := List.nil, right := w} ∧ finiteReach M c1 c2 ∧ isReject M c2))


theorem test {α : Type u} {s : Set α} {x : α} : ¬x ∈ sᶜ ↔ x ∈ s := by
  simp


theorem exDeciderIffDecidable (L : Language) : (∃ (M : Machine), isDecider M) ↔ decidable L := by
  constructor
  intro h
  rcases h with ⟨M , h⟩
  rw [decidable]
  specialize h w
  rcases h with ⟨c1, c2, hl, hr⟩
  use M
  intro w2
  use c1
  use c2
  constructor
  intro w3
  constructor
  sorry
  sorry
  sorry
  sorry

theorem exEnumeratorIffSemiDecidable (M : Machine) (L : Language) : isEnumerator M L ↔ semiDecidable L := by
  unfold isEnumerator
  unfold semiDecidable
  constructor
  intro h
  use M
  intro w
  specialize h w
  sorry
  sorry
  

theorem langSemiIffCoLangCoSemi (L : Language) : semiDecidable L ↔ coSemiDecidable (Lᶜ) := by
  constructor
  intro ⟨M, h⟩
  rw [coSemiDecidable]
  specialize h w
  rcases h with ⟨c1, c2, h⟩
  use M
  intro w2
  use c1
  use c2
  simp
  sorry
  intro ⟨M, h⟩
  rw [semiDecidable]
  specialize h w
  rcases h with ⟨c1, c2, h⟩
  simp at h
  use M
  intro w2
  use c1
  use c2
  intro wi
  sorry


theorem semiAndCoSemiIffDescidable (L : Language) : decidable L ↔ (semiDecidable L ∧ coSemiDecidable L) := by
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
  intro wl 
  exact semi wl
  unfold coSemiDecidable
  use M
  intro w
  specialize h w
  rcases h with ⟨c1, c2, semi, co_semi⟩
  use c1
  use c2
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
  use c1
  use c2
  -- exact ⟨semi_L, co_semi_L⟩
  sorry
  

  
  

  

  