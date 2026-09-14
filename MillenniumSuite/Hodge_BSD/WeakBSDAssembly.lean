import MillenniumSuite.Hodge_BSD.ArithmeticBounds

/-!
# Assembly of the weak BSD rank equality

This module is deliberately only an assembly layer.  It does not postulate the
cycle/regulator or Selmer/Euler-system estimates: it states them as separate
uniform targets and proves that once both are established for every elliptic
curve/L-function in scope, the exact `WeakBSDQ` proposition follows.
-/

noncomputable section

namespace MillenniumSuite.HodgeBSD

/-- Uniform cycle/regulator-side bound over the full weak-BSD domain. -/
def AlgebraicLowerBoundQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] [AddGroup.FG E.toAffine.Point]
    (L : ℂ → ℂ),
    IsEllipticLFunction E L → AlgebraicOrderLowerBound E L

/-- Uniform Selmer/Euler-system-side bound over the full weak-BSD domain. -/
def SelmerUpperBoundQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] [AddGroup.FG E.toAffine.Point]
    (L : ℂ → ℂ),
    IsEllipticLFunction E L → SelmerOrderUpperBound E L

/-- The two global arithmetic bounds assemble into the exact weak BSD statement. -/
theorem weakBSDQ_of_bounds
    (hlower : AlgebraicLowerBoundQ)
    (hupper : SelmerUpperBoundQ) :
    WeakBSDQ := by
  intro E _ _ L hL
  exact arithmetic_bounds_give_bsd E L (hlower E L hL) (hupper E L hL)

#print axioms MillenniumSuite.HodgeBSD.weakBSDQ_of_bounds

end MillenniumSuite.HodgeBSD
