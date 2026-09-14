import MillenniumSuite.BSD_RH.ActualZeta
import MillenniumSuite.BSD_RH.CriticalLine
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Tactic

noncomputable section

namespace MillenniumSuite.BSDRH

/-- In the positive real half-plane, a zero of `riemannZeta` is a zero of
Mathlib's completed zeta because the real Gamma factor is nonzero there. -/
theorem riemann_zero_to_completed_of_re_pos {rho : ℂ}
    (hre : 0 < rho.re)
    (hzero : riemannZeta rho = 0) :
    completedRiemannZeta rho = 0 := by
  have hrho : rho ≠ 0 := by
    intro h
    subst rho
    norm_num at hre
  have hgamma : Complex.Gammaℝ rho ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
  have hdiv : completedRiemannZeta rho / Complex.Gammaℝ rho = 0 := by
    rw [← riemannZeta_def_of_ne_zero hrho]
    exact hzero
  rcases (div_eq_zero_iff.mp hdiv) with hcomp | hgam
  · exact hcomp
  · exact (hgamma hgam).elim

/-- Hence an off-critical zero on the right feeds directly into the denominator
of the actual scattering quotient at `rho/2`. -/
theorem right_riemann_zero_gives_actual_scattering_denominator_zero
    {rho : ℂ}
    (hright : (1 / 2 : ℝ) < rho.re)
    (hzero : riemannZeta rho = 0) :
    scatteringDenominator completedRiemannZeta (rho / 2) = 0 := by
  have hre : 0 < rho.re := by linarith
  exact actual_zero_gives_scattering_denominator_zero
    (riemann_zero_to_completed_of_re_pos hre hzero)

/-- The same actual zero reflects to the left side of the critical line by
Mathlib's completed-zeta functional equation. -/
theorem right_riemann_zero_reflects_left
    {rho : ℂ}
    (hright : (1 / 2 : ℝ) < rho.re)
    (hzero : riemannZeta rho = 0) :
    completedRiemannZeta (1 - rho) = 0 ∧
      (1 - rho).re < (1 / 2 : ℝ) := by
  have hre : 0 < rho.re := by linarith
  have hcomp := riemann_zero_to_completed_of_re_pos hre hzero
  exact ⟨actual_completed_zeta_zero_symmetry hcomp,
    reflection_straddles_critical_line hright⟩

#print axioms MillenniumSuite.BSDRH.riemann_zero_to_completed_of_re_pos
#print axioms MillenniumSuite.BSDRH.right_riemann_zero_gives_actual_scattering_denominator_zero
#print axioms MillenniumSuite.BSDRH.right_riemann_zero_reflects_left

end MillenniumSuite.BSDRH
