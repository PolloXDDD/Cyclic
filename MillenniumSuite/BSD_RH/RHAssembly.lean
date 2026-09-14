import MillenniumSuite.BSD_RH.RiemannStatement

/-!
# Assembly layer for the exact Mathlib Riemann hypothesis

Mathlib defines `RiemannHypothesis` directly in terms of nontrivial zeros of
`riemannZeta`.  This module packages the remaining BSD -> RH analytic task as
exclusion of off-critical nontrivial zeros and proves that this target is
literally equivalent to the standard statement.
-/

namespace MillenniumSuite.BSDRH

/-- A nontrivial zeta zero which does not lie on `Re(s)=1/2`. -/
def IsOffCriticalNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧
  (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧
  s ≠ 1 ∧
  s.re ≠ 1 / 2

/-- Analytic target remaining after the Maass--Selberg contradiction machinery. -/
def NoOffCriticalNontrivialZeros : Prop :=
  ∀ s : ℂ, ¬ IsOffCriticalNontrivialZero s

/-- Excluding every off-critical nontrivial zero proves Mathlib's exact RH proposition. -/
theorem riemannHypothesis_of_no_off_critical_zeros
    (h : NoOffCriticalNontrivialZeros) : RiemannHypothesis := by
  intro s hz htrivial hne1
  by_contra hline
  exact h s ⟨hz, htrivial, hne1, hline⟩

/-- Conversely RH excludes exactly those zeros. -/
theorem no_off_critical_zeros_of_riemannHypothesis
    (hRH : RiemannHypothesis) : NoOffCriticalNontrivialZeros := by
  intro s hoff
  rcases hoff with ⟨hz, htrivial, hne1, hline⟩
  exact hline (hRH s hz htrivial hne1)

/-- Thus our spectral exclusion target is definitionally equivalent in content to RH. -/
theorem noOffCritical_iff_RH :
    NoOffCriticalNontrivialZeros ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_no_off_critical_zeros,
    no_off_critical_zeros_of_riemannHypothesis⟩

#print axioms MillenniumSuite.BSDRH.noOffCritical_iff_RH

end MillenniumSuite.BSDRH
