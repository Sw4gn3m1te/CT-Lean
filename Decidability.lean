import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.List
import Mathlib.Data.List.Basic


import TM


universe u

@[reducible]
def Word := List ℕ

def Word.concat (v w : Word) : Word := List.append v w
infixr:50 " + " => Word.concat

def v : Word := [1, 2, 3]
def w : Word := [4, 5]
#eval v + w

def Word.len (w: Word) : ℕ :=
  w.length

@[reducible]
def Language := Set Word


theorem lCompIff  (L : Language) : ∀ (w : Word),  (w ∈ L ↔ w ∉ Lᶜ) := by
  intro w
  rw [Set.mem_compl_iff]
  simp


def isDecider (M : Machine) : Prop := 
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧
    finiteReach M c1 c2

-- 
def isEnumerator (M : Machine) (L : Language) : Prop :=
  ∀ (w : Word), w ∈ L → ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ 
    isAccept M c2 → finiteReach M c1 c2


-- is assuming unreachable F's dont exits ok ?
def isSemiDecider (M : Machine) : Prop :=
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ 
    isAccept M c2 → finiteReach M c1 c2

def isCoSemiDecider (M : Machine) : Prop :=
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ 
    isReject M c2 → finiteReach M c1 c2

def semiDecidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg),
    (w ∈ L → c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ finiteReach M c1 c2 ∧ isAccept M c2)

def coSemiDecidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg),
    (w ∉ L → c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ finiteReach M c1 c2 ∧ isReject M c2)

def decidable (L : Language) : Prop := 
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg), 
    ((w ∈ L → c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ finiteReach M c1 c2 ∧ isAccept M c2) ∧ 
    (w ∉ L → c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ finiteReach M c1 c2 ∧ isReject M c2))


theorem test {α : Type u} {s : Set α} {x : α} : ¬x ∈ sᶜ ↔ x ∈ s := by
  simp


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
  constructor
  intro w
  sorry
  sorry
  -- construct Machine how ?

  
  

  

  