import MillenniumSuite.BSD_RH.ZetaZeroTransfer
import MillenniumSuite.BSD_RH.MaassSelbergPositivity

/-!
# Spectral obstruction for right-half zeta zeros

The difficult analytic content is kept as an explicit target proposition:
for every right-half zeta zero, the scattering construction must produce a
nonzero residue and the Maass--Selberg norm identity.  Once that is supplied,
Lean closes the contradiction with the already proved positivity lemma.
-/

namespace MillenniumSuite.BSDRH

/-- Exact remaining spectral datum needed to exclude a right-half zeta zero. -/
def RightZeroProducesMaassSelbergData : Prop :=
  ∀ rho : ℂ,
    (1 / 2 : ℝ) < rho.re →
    riemannZeta rho = 0 →
    ∃ normSq R : ℝ,
      0 ≤ normSq ∧
      R ≠ 0 ∧
      normSq = residueTerm R rho.re

/-- Under the spectral residue target, no zeta zero can lie strictly right of
`Re(s)=1/2`. -/
theorem no_right_riemann_zero
    (hspectral : RightZeroProducesMaassSelbergData) :
    ∀ rho : ℂ, riemannZeta rho = 0 → ¬ ((1 / 2 : ℝ) < rho.re) := by
  intro rho hzero hright
  rcases hspectral rho hright hzero with ⟨normSq, R, hnorm, hR, heq⟩
  exact maass_selberg_positivity_contradiction hnorm hR hright heq

/-- Equivalent formulation as a universal real-part upper bound on zeta zeros. -/
theorem zeta_zero_re_le_half_of_spectral_data
    (hspectral : RightZeroProducesMaassSelbergData)
    (rho : ℂ) (hzero : riemannZeta rho = 0) :
    rho.re ≤ (1 / 2 : ℝ) := by
  exact le_of_not_gt (no_right_riemann_zero hspectral rho hzero)

#print axioms MillenniumSuite.BSDRH.no_right_riemann_zero
#print axioms MillenniumSuite.BSDRH.zeta_zero_re_le_half_of_spectral_data

end MillenniumSuite.BSDRH
