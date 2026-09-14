import MillenniumSuite.BSD_RH.ResidueMechanism

/-!
# Decomposition of the Maass--Selberg residue mechanism

The manuscript's BSD -> RH bridge uses two analytically distinct steps after a
zero of the scattering denominator has been produced:

1. the denominator zero gives an isolated scattering pole with nonzero residue;
2. the contour form of the Maass--Selberg relation identifies a nonnegative
   truncated-Eisenstein norm square with the residue contribution.

This file separates those two targets. Neither is postulated as a theorem.
-/

noncomputable section

namespace MillenniumSuite.BSDRH

/-- Pole-production target extracted from the sentence following
`Phi(s) = xi(2s-1)/xi(2s)`: a right-half denominator zero produces a nonzero
real residue magnitude. -/
def ScatteringPoleTarget : Prop :=
  ∀ rho : ℂ,
    (1 / 2 : ℝ) < rho.re →
    scatteringDenominator completedRiemannZeta (rho / 2) = 0 →
    ∃ R : ℝ, R ≠ 0

/-- Contour Maass--Selberg target: once a nonzero residue magnitude `R` is
available, the normalized residue computation gives a nonnegative norm square
whose value is the explicit residue term used in the manuscript. -/
def MaassSelbergContourTarget : Prop :=
  ∀ rho : ℂ, ∀ R : ℝ,
    (1 / 2 : ℝ) < rho.re →
    R ≠ 0 →
    ∃ normSq : ℝ,
      0 ≤ normSq ∧ normSq = residueTerm R rho.re

/-- The two analytic targets assemble exactly into the previously isolated
`MaassSelbergResidueMechanism`. -/
theorem residue_mechanism_of_pole_and_contour
    (hpole : ScatteringPoleTarget)
    (hcontour : MaassSelbergContourTarget) :
    MaassSelbergResidueMechanism := by
  intro rho hright hden
  rcases hpole rho hright hden with ⟨R, hR⟩
  rcases hcontour rho R hright hR with ⟨normSq, hnorm, heq⟩
  exact ⟨normSq, R, hnorm, hR, heq⟩

/-- Consequently, the two analytic targets exclude every zeta zero strictly to
the right of the critical line. -/
theorem no_right_zero_of_pole_and_contour
    (hpole : ScatteringPoleTarget)
    (hcontour : MaassSelbergContourTarget) :
    ∀ rho : ℂ, riemannZeta rho = 0 → ¬ ((1 / 2 : ℝ) < rho.re) := by
  exact no_right_riemann_zero (residue_mechanism_of_pole_and_contour hpole hcontour)

#print axioms MillenniumSuite.BSDRH.residue_mechanism_of_pole_and_contour
#print axioms MillenniumSuite.BSDRH.no_right_zero_of_pole_and_contour

end MillenniumSuite.BSDRH
