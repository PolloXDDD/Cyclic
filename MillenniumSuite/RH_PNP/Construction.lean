import MillenniumSuite.RH_PNP.ProblemStatement

/-!
# Explicit SAT penalty construction

No `axiom`, `constant`, `sorry`, certificate record, or external correctness
hypothesis is used.  The penalty is a literal recursive definition.
-/

set_option autoImplicit false

namespace MillenniumSuite.RHPNP

/-- A literal contributes zero precisely when it is satisfied and one otherwise. -/
def literalPenalty {n : Nat} (a : Assignment n) (lit : Literal n) : Nat :=
  if Literal.eval a lit = true then 0 else 1

/-- Product of literal penalties.  Thus a clause has penalty zero exactly when
at least one literal is satisfied. -/
def clausePenalty {n : Nat} (a : Assignment n) : Clause n -> Nat
  | [] => 1
  | lit :: C => literalPenalty a lit * clausePenalty a C

/-- Sum of clause penalties.  Thus the formula has penalty zero exactly when
every clause has penalty zero. -/
def formulaPenalty {n : Nat} (a : Assignment n) : CNF n -> Nat
  | [] => 0
  | C :: F => clausePenalty a C + formulaPenalty a F

end MillenniumSuite.RHPNP
