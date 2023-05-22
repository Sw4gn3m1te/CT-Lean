import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.List
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Prod.Basic
import Mathlib.Data.List.Basic
import «TM»

universe u

namespace TM

structure Word where
  data : List ℕ

def Word.concat (v w : Word) : Word :=
  {data := v.data ++ w.data}

def Word.len (w: Word) : ℕ :=
  w.data.length

def Language := Set Word

-- failed to synth. instance membership Word Language ?
def Language.complement (L : Language) : Language := λ w => ¬ (w ∈ L) 

  
def isDecider (M : Machine) : Prop := 
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil,  right := w.data} ∧
    finiteReach M c1 c2


-- is assuming unreachable F's dont exits ok ?
def isEnumerator (M : Machine) : Prop :=
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = {state := 0, head := 0, left := List.nil,  right := w.data} ∧ 
    isFinal M c2 → finiteReach M c1 c2


-- failed to synth. membership ?
def decidable (L : Language) : Prop := 
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg), 
    (w.data ∈ L → c1 = {state := 0, head := 0, left := List.nil,  right := w.data} ∧ finiteReach M c1 c2 ∧ isFinal M c2) ∧ 
    (w.data ∉ L → c1 = {state := 0, head := 0, left := List.nil,  right := w.data} ∧ finiteReach M c1 c2 ∧ ¬ isFinal M c2)


def semi_descidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg),
    (w.data ∈ L → c1 = {state := 0, head := 0, left := List.nil,  right := w.data} ∧ finiteReach M c1 c2 ∧ isFinal M c2)


def co_semi_descidable (L : Language) : Prop :=
  ∃ (M : Machine), ∀ (w : Word), ∃ (c1 c2 : Cfg),
    (w.data ∉ L → c1 = {state := 0, head := 0, left := List.nil,  right := w.data} ∧ finiteReach M c1 c2 ∧ ¬ isFinal M c2)



theorem exEnumeratoreqSemiDecidable (M : Machine) (L : Language) : isEnumerator M ↔ semi_descidable L :=
  sorry

theorem LangSemiEqCoLangCoSemi (L : Language) : semi_descidable L ↔ co_semi_descidable L.complement :=
  sorry

theorem co_semi_and_semi_is_descidable (L : Language) : decidable L ↔ semi_descidable L ∧ co_semi_descidable L :=
  -- ∀ w sim M and fin reach M w 
  sorry







