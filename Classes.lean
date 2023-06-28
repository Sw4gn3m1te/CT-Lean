import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Real.Basic


import TM
import Language



-- def g on reals ?
def fEqOg (f : ℕ → ℕ) (g : ℝ → ℝ) : Prop :=
  ∃ (c : ℝ), ∃ (n0 : ℕ), ∀ (n : ℕ), c > 0 ∧ n > n0 → f n ≤ c * g n

def fEqog (f : ℕ → ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ (c : ℝ), ∃ (n0 : ℕ), ∀ (n : ℕ), c > 0 ∧ n > n0 → f n ≤ c * g n 

def fEqΘg (f : ℕ → ℕ) (g : ℝ → ℝ) : Prop :=
  ∃ (c1 c2 : ℝ), ∃ (n0 : ℕ), ∀ (n : ℕ), c1 > 0 ∧ c1 > 0 ∧ n > n0 → c1 * g n ≤ f n ∧ f n ≤ c2 * g n

def fEqΩg (f : ℕ → ℕ) (g : ℝ → ℝ) : Prop :=
  ∃ (c : ℝ), ∃ (n0 : ℕ), ∀ (n : ℕ), c > 0 ∧ n > n0 → f n ≥ c * g n

def fEqωg (f : ℕ → ℕ) (g : ℝ → ℝ) : Prop :=
  ∀ (c : ℝ), ∃ (n0 : ℕ), ∀ (n : ℕ), c > 0 ∧ n > n0 → f n ≥ c * g n


def mIsBoundedByF (M : Machine) (f : ℕ → ℕ) : Prop :=
  ∀ (w : Word), ∃ (c1 c2 : Cfg), c1 = startCfg M w ∧ reachN M (f w.length) c1 c2 ∧ mHaltsOnW M w

def mIsBoundedbyOg (M : Machine) (g : ℝ → ℝ) : Prop := 
  ∃ (f : ℕ → ℕ), mIsBoundedByF M f ∧ fEqOg f g 


def DTime (g : ℝ → ℝ) : Set Language :=
  { languageOfMachine M | ∀ (M : DTM), mIsBoundedbyOg M g}
