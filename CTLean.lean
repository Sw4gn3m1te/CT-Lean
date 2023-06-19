import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.List
import Mathlib.Data.List.Basic


-- Q : States
-- Λ : Inp Alph
-- Γ : Tape Alph
-- F : Fin States

-- Tm must dynamicly allocate memory when moving out of defined tape list
-- decidability of M.δ

import TM
import Language
import Decidability

def L1 : Language := {[1], [1,1], [1,1,1], [1,1,1,1]}
def L2 : Language := {[1], [1,2], [1,1,1], [1,2,1,2], [1,1,1,1,1]}


def TmL1 : Machine := {Q:= Finset.range 6, Λ:= Finset.range 2, Γ:= Finset.range 3, F:= {1,2,3,4}, q0:= 0,
                       δ:= fun (q, γ) => (if (q<4 ∧ γ == 1) then (q + 1, 1, Direction.R) else (5, γ, Direction.N))}


def TmL2 : Machine := {Q:= Finset.range 7, Λ:= Finset.range 3, Γ:= Finset.range 4, F:= {1,2,3,4,5}, q0:= 0,
                       δ:= fun (q, γ) => (if (q%2 == 1 ∧ γ == 1 ∧ q<9) then (q+1, γ, Direction.R)
                        else if (q%2 == 1 ∧ γ == 1 ∧ q<5) then (q+1, γ, Direction.R)
                        else (5, γ, Direction.N))}

                           

def startTmL1 := startCfg TmL1 [1,1,1]


def o1 := stepMOnC TmL1 startTmL1
def o2 := stepMOnC TmL1 o1
def o3 := stepMOnC TmL1 o2
def o4 := stepMOnC TmL1 o3
def o5 := stepMOnC TmL1 o4

#eval (startTmL1.state, startTmL1.head, startTmL1.left, startTmL1.right)
#eval (o1.state, o1.head, o1.left, o1.right)
#eval (o2.state, o2.head, o2.left, o2.right)
#eval (o3.state, o3.head, o3.left, o3.right)
#eval (o4.state, o4.head, o4.left, o4.right)
#eval (o5.state, o5.head, o5.left, o5.right)

def x := o5
#eval ((TmL1.δ (x.state, x.right.head!)).fst, (TmL1.δ (x.state, x.right.head!)).snd.fst,  directionToNum (TmL1.δ (x.state, x.right.head!)).snd.snd)
--  = (o1.state, o1.right.head!, Direction.N)
-- #eval isFinal TmL1 o2


def TMExample : Machine := {Q:= Finset.range 3, Λ:= Finset.range 3, Γ:= Finset.range 3, F:= Finset.empty, q0:= 1,
                            δ := fun (q, γ) => ((q + 1) % 5, (γ + 1) % 26, Direction.L)}

def TMExample2 : Machine := {Q:= Finset.range 4, Λ:= Finset.range 4, Γ:= Finset.range 4, F:= Finset.empty, q0:= 1,
                             δ := fun (q, γ) => ((q + 1) % 5, (γ + 1) % 26, Direction.L)}

def v : Word := [1, 2, 3]
def w : Word := [3, 4]
