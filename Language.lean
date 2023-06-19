import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.List
import Mathlib.Data.List.Basic




@[reducible]
def Word := List ℕ

def Word.concat (v w : Word) : Word := List.append v w
infixr:50 " + " => Word.concat


def Word.len (w: Word) : ℕ :=
  w.length

@[reducible]
def Language := Set Word