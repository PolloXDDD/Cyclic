import MillenniumSuite.BSD_RH.ZetaZeroTransfer
import MillenniumSuite.BSD_RH.MaassSelbergPositivity

noncomputable section

namespace MillenniumSuite.BSDRH

/-- Exact spectral obligation extracted from the manuscript: once the actual
scattering denominator vanishes at `rho/2` to the right of the critical line,
the Maass--Selberg residue computation supplies a nonnegative norm square equal
to a nonzero-residue term.  This is a target proposition, not an asserted fact. -/
def MaassSelbergResidueMechanism : Prop :=
  ∀ rho : ℂ,
    (1 / 2 : ℝ) < rho.re →
    scatteringDenominator completedRiemannZeta (rho / 2) = 0 →
    ∃ normSq R : ℝ,
      0 ≤ normSq ∧ R ≠ 0 ∧ normSq = residueTerm R rho.re

/-- Once the residue mechanism is established, no Riemann-zeta zero can occur
to the right of the critical line. -/
theorem no_right_riemann_zero_of_residue_mechanism
    (hMS : MaassSelbergResidueMechanism)
    {rho : ℂ}
    (hright : (1 / 2 : ℝ) < rho.re)
    (hzero : riemannZeta rho = 0) : False := by
  have hden : scatteringDenominator completedRiemannZeta (rho / 2) = 0 :=
    right_riemann_zero_gives_actual_scattering_denominator_zero hright hzero
  rcases hMS rho hright hden with ⟨normSq, R, hnorm, hR, heq⟩
  exact maass_selberg_positivity_contradiction hnorm hR hright heq

/-- Equivalent exclusion form useful when assembling the RH endpoint. -/
theorem no_right_riemann_zero
    (hMS : MaassSelbergResidueMechanism) :
    ∀ rho : ℂ, riemannZeta rho = 0 → ¬ ((1 / 2 : ℝ) < rho.re) := by
  intro rho hzero hright
  exact no_right_riemann_zero_of_residue_mechanism hMS hright hzero

#print axioms MillenniumSuite.BSDRH.no_right_riemann_zero_of_residue_mechanism
#print axioms MillenniumSuite.BSDRH.no_right_riemann_zero

end MillenniumSuite.BSDRH
