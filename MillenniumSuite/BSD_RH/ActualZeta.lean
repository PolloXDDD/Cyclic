import MillenniumSuite.BSD_RH.Scattering
import Mathlib.NumberTheory.LSeries.RiemannZeta

noncomputable section

namespace MillenniumSuite.BSDRH

/-- Mathlib's completed Riemann zeta satisfies exactly the functional equation
used in the manuscript. -/
theorem actual_completed_zeta_functional_equation :
    FunctionalEquation completedRiemannZeta := by
  intro s
  exact (completedRiemannZeta_one_sub s).symm

/-- A zero of Mathlib's completed Riemann zeta is reflected to `1-rho`. -/
theorem actual_completed_zeta_zero_symmetry {rho : ℂ}
    (hzero : completedRiemannZeta rho = 0) :
    completedRiemannZeta (1 - rho) = 0 := by
  rw [completedRiemannZeta_one_sub rho, hzero]

/-- For the actual completed zeta, a zero `rho` makes the denominator of the
manuscript's scattering quotient vanish at `rho/2`. -/
theorem actual_zero_gives_scattering_denominator_zero {rho : ℂ}
    (hzero : completedRiemannZeta rho = 0) :
    scatteringDenominator completedRiemannZeta (rho / 2) = 0 := by
  exact zero_gives_scattering_denominator_zero completedRiemannZeta rho hzero

#print axioms MillenniumSuite.BSDRH.actual_completed_zeta_functional_equation
#print axioms MillenniumSuite.BSDRH.actual_completed_zeta_zero_symmetry
#print axioms MillenniumSuite.BSDRH.actual_zero_gives_scattering_denominator_zero

end MillenniumSuite.BSDRH
