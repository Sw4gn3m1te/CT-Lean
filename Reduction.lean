import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.List
import Mathlib.Data.List.Basic

import Language
import Decidability


universe u

@[reducible]
def RedFunction := Word → Word

def FIsL1MRedToL2 (f : RedFunction) (L1 L2 : Language) : Prop :=
  ∀ (w : Word), (w ∈ L1 ↔ f w ∈ L2)

theorem te (f : RedFunction) (L1 L2 : Language) : (FIsL1MRedToL2 f L1 L2) ↔ (∀ w, (w ∈ L1 ∧ f w ∈ L2)):= by
  rw [FIsL1MRedToL2]
  constructor
  intro h w
  specialize h w
  rw [← h]
  simp
  sorry
  intro h w
  specialize h w
  tauto

theorem redToDecidable (L1 L2 : Language) (f : RedFunction) : FIsL1MRedToL2 f L1 L2 ∧ decidable L2 → decidable L1 := by
  intro ⟨hl, M, hr⟩
  rw [decidable]
  use M
  intro w
  specialize hr w
  rcases hr with ⟨c1, c2, win, wout⟩
  use c1, c2
  constructor
  rw [FIsL1MRedToL2] at hl
  specialize hl w
  intro wl1
  rw [hl] at wl1  
  sorry
  intro notwL1
  sorry
  
  

  

theorem redToSemiDecidable (L1 L2 : Language) (f: RedFunction) : FIsL1MRedToL2 f L1 L2 ∧ semiDecidable L2 → semiDecidable L1 := by
  sorry