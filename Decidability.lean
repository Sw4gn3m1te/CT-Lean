import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.List
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic

import «TM»

universe u

namespace TM


def Word := List ℕ

def Word.concat (v w : Word) : Word := List.append v w
infixr:50 " + " => Word.concat

def v : Word := [1, 2, 3]
def w : Word := [4, 5]
#eval v + w

def Word.len (w: Word) : ℕ :=
  w.length

def Language := Set Word

def Language.element (w : Word) (L : Set Word) : Prop := L w
infixr:75 " ∈ " => Language.element

-- failed to synth. instance membership Word Language ?
def Language.complement (L : Language) : Language := λ w => ¬ (w ∈ L) 

def Language.notElement (w : Word) (L : Language) : Prop := L w
infixr: 75 "∉" => Language.notElement 
  
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


def semi_decidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg),
    (w ∈ L → c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ finiteReach M c1 c2 ∧ isAccept M c2)

def co_semi_decidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg),
    (w ∉ L → c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ finiteReach M c1 c2 ∧ isReject M c2)

def decidable (L : Language) : Prop := 
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg), 
    ((w ∈ L → c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ finiteReach M c1 c2 ∧ isAccept M c2) ∧ 
    (w ∉ L → c1 = {state := 0, head := 0, left := List.nil,  right := w} ∧ finiteReach M c1 c2 ∧ isReject M c2))


theorem exEnumeratoreqSemiDecidable (M : Machine) (L : Language) : isEnumerator M L ↔ semi_decidable L := by
  constructor
  unfold isEnumerator
  intro h
  specialize h w
  unfold semi_decidable
  use M
  sorry

  

theorem LangSemiEqCoLangCoSemi (L : Language) : semi_decidable L ↔ co_semi_decidable L.complement := by
  constructor
  intro ⟨M, h⟩
  specialize h w
  rcases h with ⟨c1, c2, h⟩
  sorry


theorem CoSemiAndSemiEqDescidable (L : Language) : decidable L ↔ (semi_decidable L ∧ co_semi_decidable L) := by
  constructor
  intro ⟨M, h⟩
  constructor
  unfold semi_decidable
  use M
  intro w
  specialize h w
  rcases h with ⟨c1, c2, semi, co_semi⟩
  use c1
  use c2 
  intro wl 
  exact semi wl
  unfold co_semi_decidable
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
  -- construct Machine how ?




  
  
  
  

  

  