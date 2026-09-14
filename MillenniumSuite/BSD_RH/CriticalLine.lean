import MillenniumSuite.BSD_RH.Scattering
import Mathlib.Tactic

namespace MillenniumSuite.BSDRH

/-- Reflection `rho ↦ 1-rho` sends a point strictly to the right of the
critical line to one strictly to the left. -/
theorem reflection_straddles_critical_line {rho : ℂ}
    (h : (1 / 2 : ℝ) < rho.re) :
    (1 - rho).re < (1 / 2 : ℝ) := by
  have hr : (1 : ℝ) - rho.re < (1 / 2 : ℝ) := by
    linarith
  simpa using hr

/-- Combining the functional equation with the real-part calculation gives the
symmetric off-line zero used in the manuscript's contradiction setup. -/
theorem symmetric_zero_left_of_line
    (xi : CompletedZeta) (rho : ℂ)
    (hFE : FunctionalEquation xi) (hzero : IsZero xi rho)
    (hright : (1 / 2 : ℝ) < rho.re) :
    IsZero xi (1 - rho) ∧ (1 - rho).re < (1 / 2 : ℝ) := by
  exact ⟨functional_equation_zero_symmetry xi rho hFE hzero,
    reflection_straddles_critical_line hright⟩

#print axioms MillenniumSuite.BSDRH.symmetric_zero_left_of_line

end MillenniumSuite.BSDRH
