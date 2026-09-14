import MillenniumSuite.BSD_RH.ProblemStatement
import Mathlib.Tactic

namespace MillenniumSuite.BSDRH

/-- The functional equation alone reflects every zero across `s ↦ 1-s`. -/
theorem functional_equation_zero_symmetry : ZeroSymmetryTarget := by
  intro xi rho hFE hzero
  unfold IsZero at *
  calc
    xi (1 - rho) = xi rho := (hFE rho).symm
    _ = 0 := hzero

/-- If `rho` is a zero, then `s = rho/2` zeros the denominator `xi(2s)` of
`Phi(s) = xi(2s-1)/xi(2s)`, exactly as in the manuscript. -/
theorem zero_gives_scattering_denominator_zero
    (xi : CompletedZeta) (rho : ℂ) (hzero : IsZero xi rho) :
    scatteringDenominator xi (rho / 2) = 0 := by
  unfold scatteringDenominator IsZero at *
  have hscale : (2 : ℂ) * (rho / 2) = rho := by ring
  rw [hscale]
  exact hzero

#print axioms MillenniumSuite.BSDRH.functional_equation_zero_symmetry
#print axioms MillenniumSuite.BSDRH.zero_gives_scattering_denominator_zero

end MillenniumSuite.BSDRH
