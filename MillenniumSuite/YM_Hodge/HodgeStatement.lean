import Mathlib

/-!
# Quantified Hodge statement

Mathlib does not currently provide the full package of Chow groups, Hodge
structures, and cycle-class maps needed for the Clay statement in one ready-made
API.  This file therefore gives a semantic interface with the exact quantifier
shape needed by the manuscript, without asserting the conjecture.
-/

universe u v

namespace MillenniumSuite.YMHodge

/-- Semantic data required to state the Hodge conjecture. -/
structure HodgeModel where
  Variety : Type u
  CohomologyClass : Variety → ℕ → Type v
  SmoothProjective : Variety → Prop
  RationalHodgeClass : ∀ X p, CohomologyClass X p → Prop
  AlgebraicCycleClass : ∀ X p, CohomologyClass X p → Prop

/-- Every rational `(p,p)` Hodge class on every smooth projective variety is algebraic. -/
def HodgeConjecture (M : HodgeModel) : Prop :=
  ∀ (X : M.Variety), M.SmoothProjective X →
    ∀ (p : ℕ) (alpha : M.CohomologyClass X p),
      M.RationalHodgeClass X p alpha → M.AlgebraicCycleClass X p alpha

/-- The exact implication shape of Transduction III. -/
def YMHodgeBridgeTarget (MassGap : Prop) (M : HodgeModel) : Prop :=
  MassGap → HodgeConjecture M

end MillenniumSuite.YMHodge
