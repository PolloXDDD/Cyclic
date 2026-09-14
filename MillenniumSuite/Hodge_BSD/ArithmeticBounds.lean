import MillenniumSuite.Hodge_BSD.ArithmeticStatement

noncomputable section

namespace MillenniumSuite.HodgeBSD

open scoped Topology

/-- Regulator/cycle side: Mordell--Weil free rank is at most the analytic order. -/
def AlgebraicOrderLowerBound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [AddGroup.FG E.toAffine.Point]
    (L : ℂ → ℂ) : Prop :=
  AddCommGroup.freeRank E.toAffine.Point ≤ meromorphicOrderAt L 1

/-- Euler-system/Selmer side: analytic order is at most the Mordell--Weil free rank. -/
def SelmerOrderUpperBound
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [AddGroup.FG E.toAffine.Point]
    (L : ℂ → ℂ) : Prop :=
  meromorphicOrderAt L 1 ≤ AddCommGroup.freeRank E.toAffine.Point

/-- The two exact arithmetic inequalities force the weak BSD rank equality. -/
theorem arithmetic_bounds_give_bsd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] [AddGroup.FG E.toAffine.Point]
    (L : ℂ → ℂ)
    (hlower : AlgebraicOrderLowerBound E L)
    (hupper : SelmerOrderUpperBound E L) :
    meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point := by
  exact le_antisymm hupper hlower

#print axioms MillenniumSuite.HodgeBSD.arithmetic_bounds_give_bsd

end MillenniumSuite.HodgeBSD
