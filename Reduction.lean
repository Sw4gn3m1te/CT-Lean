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

