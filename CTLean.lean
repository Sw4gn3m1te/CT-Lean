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


def TmL1 : Dtm := {Q:= Finset.range 6, Λ:= Finset.range 2, Γ:= Finset.range 3, F:= {1,2,3,4}, q0:= 0,
                       δ:= fun (q, γ) => (if (q<4 ∧ γ == 1) then (q + 1, 1, Direction.R) else (5, γ, Direction.N)),
                       FInQ := by simp, uniqueness := by sorry}


def TmL2 : Dtm := {Q:= Finset.range 7, Λ:= Finset.range 3, Γ:= Finset.range 4, F:= {1,2,3,4,5}, q0:= 0,
                       δ:= fun (q, γ) => (if (q%2 == 1 ∧ γ == 1 ∧ q<9) then (q+1, γ, Direction.R)
                        else if (q%2 == 1 ∧ γ == 1 ∧ q<5) then (q+1, γ, Direction.R)
                        else (5, γ, Direction.N)),
                        FInQ := by simp, uniqueness := by sorry}

-- B = 0, 0 = 1, X = 2, C = 3
def TmL3 : Dtm := {Q := Finset.range 7, Λ := Finset.range 3, Γ := Finset.range 4, F := {6}, q0 := 0,
                        δ := fun (q, γ) => (if (q == 0 ∧ γ == 1) then (1, 2, Direction.R)
                                       else if (q == 0 ∧ γ == 3) then (2, 3, Direction.R)
                                       else if (q == 1 ∧ γ == 1) then (1, 1, Direction.R)
                                       else if (q == 1 ∧ γ == 3) then (2, 3, Direction.R)
                                       else if (q == 2 ∧ γ == 1) then (2, 1, Direction.R)
                                       else if (q == 2 ∧ γ == 0) then (3, 0, Direction.L)
                                       else if (q == 3 ∧ γ == 1) then (4, 0, Direction.L)
                                       else if (q == 3 ∧ γ == 3) then (5, 0, Direction.L)
                                       else if (q == 4 ∧ γ == 1) then (4, 1, Direction.L)
                                       else if (q == 4 ∧ γ == 3) then (5, 1, Direction.L)
                                       else if (q == 5 ∧ γ == 1) then (5, 1, Direction.L)
                                       else if (q == 5 ∧ γ == 2) then (6, 1, Direction.N)
                                       else (q, γ, Direction.N)),
                                      FInQ := by simp, uniqueness := by sorry}

#eval (prodM TmL1 TmL2).Q

def startTmL1 := startCfg TmL1 [1,1,1]

def startTmL3 := startCfg TmL3 [1,1,1,3,1,1,0,0,0,0,0,0,0]


def o1 := stepMOnC TmL3 startTmL3
def o2 := stepMOnC TmL3 o1
def o3 := stepMOnC TmL3 o2
def o4 := stepMOnC TmL3 o3
def o5 := stepMOnC TmL3 o4
def o6 := stepMOnC TmL3 o5
def o7 := stepMOnC TmL3 o6
def o8 := stepMOnC TmL3 o7
def o9 := stepMOnC TmL3 o8
def o10 := stepMOnC TmL3 o9
def o11 := stepMOnC TmL3 o10
def o12 := stepMOnC TmL3 o11
def o13 := stepMOnC TmL3 o12
def o14 := stepMOnC TmL3 o13
def o15 := stepMOnC TmL3 o14
def o16 := stepMOnC TmL3 o15

#eval (startTmL3.state, startTmL3.head, startTmL3.left, startTmL3.right)
#eval (o1.state, o1.head, o1.left, o1.right)
#eval (o2.state, o2.head, o2.left, o2.right)
#eval (o3.state, o3.head, o3.left, o3.right)
#eval (o4.state, o4.head, o4.left, o4.right)
#eval (o5.state, o5.head, o5.left, o5.right)
#eval (o6.state, o6.head, o6.left, o6.right)
#eval (o7.state, o7.head, o7.left, o7.right)
#eval (o8.state, o8.head, o8.left, o8.right)
#eval (o9.state, o9.head, o9.left, o9.right)
#eval (o10.state, o10.head, o10.left, o10.right)
#eval (o11.state, o11.head, o11.left, o11.right)
#eval (o12.state, o12.head, o12.left, o12.right)
#eval (o13.state, o13.head, o13.left, o13.right)
#eval (o14.state, o14.head, o14.left, o14.right)
#eval (o15.state, o15.head, o15.left, o15.right)
#eval (o16.state, o16.head, o16.left, o16.right)

def runTmL3 := run


def x := o5
#eval ((TmL1.δ (x.state, x.right.head!)).fst, (TmL1.δ (x.state, x.right.head!)).snd.fst,  directionToNum (TmL1.δ (x.state, x.right.head!)).snd.snd)
--  = (o1.state, o1.right.head!, Direction.N)
-- #eval isFinal TmL1 o2


def TMExample : Machine := {Q:= Finset.range 3, Λ:= Finset.range 3, Γ:= Finset.range 3, F:= Finset.empty, q0:= 1,
                            δ := fun (q, γ) => ((q + 1) % 5, (γ + 1) % 26, Direction.L),
                            FInQ := by simp}

def TMExample2 : Machine := {Q:= Finset.range 4, Λ:= Finset.range 4, Γ:= Finset.range 4, F:= Finset.empty, q0:= 1,
                             δ := fun (q, γ) => ((q + 1) % 5, (γ + 1) % 26, Direction.L),
                             FInQ := by simp}

def v : Word := [1, 2, 3]
def w : Word := [3, 4]
