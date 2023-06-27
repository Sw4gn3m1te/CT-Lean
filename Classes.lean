import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval

import TM
import Language


def mAcceptsWInPoly (M : Machine) (w : Word) : Prop :=
  ∃ (p : Polynomial ℕ), ∃ (c1 c2 : Cfg), c1 = startCfg M w ∧ reachN M (p.eval₂ w.length) c1 c2 ∧ isAccept M c2 ∧ isFinal M c2
