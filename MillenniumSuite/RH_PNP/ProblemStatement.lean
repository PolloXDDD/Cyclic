import Mathlib.Data.List.Basic

/-!
# RH -> P=NP bridge: exact finite SAT subproblem

This module follows the statement/solution separation used by
`openai/NavierStokesAndEuler`: it defines the mathematical target but proves
nothing by postulate.

The purpose of this slice is to formalize the exact zero-penalty encoding of a
CNF formula.  It is one concrete component needed by any later formalization of
the manuscript's RH -> P=NP transduction.
-/

set_option autoImplicit false

namespace MillenniumSuite.RHPNP

inductive Literal (n : Nat) where
  | pos : Fin n -> Literal n
  | neg : Fin n -> Literal n
  deriving DecidableEq, Repr

abbrev Assignment (n : Nat) := Fin n -> Bool
abbrev Clause (n : Nat) := List (Literal n)
abbrev CNF (n : Nat) := List (Clause n)

def Literal.eval {n : Nat} (a : Assignment n) : Literal n -> Bool
  | .pos i => a i
  | .neg i => !(a i)

def ClauseSatisfied {n : Nat} (a : Assignment n) (C : Clause n) : Prop :=
  ∃ lit ∈ C, Literal.eval a lit = true

def FormulaSatisfied {n : Nat} (a : Assignment n) (F : CNF n) : Prop :=
  ∀ C ∈ F, ClauseSatisfied a C

def Satisfiable {n : Nat} (F : CNF n) : Prop :=
  ∃ a : Assignment n, FormulaSatisfied a F

/-- Target of this formalization slice: a concrete penalty function detects
satisfiability exactly by attaining zero. -/
def ZeroPenaltyEncodingStatement : Prop :=
  ∃ penalty : {n : Nat} -> Assignment n -> CNF n -> Nat,
    ∀ {n : Nat} (F : CNF n),
      Satisfiable F ↔ ∃ a : Assignment n, penalty a F = 0

end MillenniumSuite.RHPNP
