import MillenniumSuite.YM_Hodge.ProblemStatement

namespace MillenniumSuite.YMHodge

/-- At the topological minimum, the sum of the two squared residual terms is zero. -/
theorem residual_square_sum_zero {d : EnergyData}
    (hE : EnergyIdentity d) (hmin : AtTopologicalMinimum d) :
    2 * d.residual02 ^ 2 + d.residualHE ^ 2 = 0 := by
  unfold EnergyIdentity AtTopologicalMinimum at hE hmin
  nlinarith

/-- The manuscript's Hermitian--Einstein conclusion follows algebraically from
its displayed energy decomposition once absolute minimality has been reached. -/
theorem minimum_forces_hermitian_einstein : MinimumForcesHermitianEinstein := by
  intro d hE hmin
  have hsum := residual_square_sum_zero hE hmin
  have h02 : 0 ≤ d.residual02 ^ 2 := sq_nonneg d.residual02
  have hHE : 0 ≤ d.residualHE ^ 2 := sq_nonneg d.residualHE
  constructor <;> nlinarith

#print axioms MillenniumSuite.YMHodge.minimum_forces_hermitian_einstein

end MillenniumSuite.YMHodge
