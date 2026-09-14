import Mathlib.Data.Complex.Basic

/-!
# BSD -> RH: completed-zeta / scattering layer

This module formalizes the exact analytic objects used in Transduction V at the
level needed for the first spectral lemmas: a completed zeta function, its
functional equation, zeros, and the scattering quotient
`Phi(s) = xi(2s-1) / xi(2s)`.
-/

noncomputable section

namespace MillenniumSuite.BSDRH

abbrev CompletedZeta := ℂ → ℂ

/-- Functional equation `xi(s) = xi(1-s)`. -/
def FunctionalEquation (xi : CompletedZeta) : Prop :=
  ∀ s : ℂ, xi s = xi (1 - s)

/-- A zero of the completed zeta function. -/
def IsZero (xi : CompletedZeta) (rho : ℂ) : Prop :=
  xi rho = 0

/-- The scalar scattering function from the manuscript. -/
def scattering (xi : CompletedZeta) (s : ℂ) : ℂ :=
  xi (2 * s - 1) / xi (2 * s)

/-- Its denominator, isolated because zero ordinates are mapped to denominator zeros. -/
def scatteringDenominator (xi : CompletedZeta) (s : ℂ) : ℂ :=
  xi (2 * s)

/-- Symmetry of zeros under `rho ↦ 1-rho`. -/
def ZeroSymmetryTarget : Prop :=
  ∀ (xi : CompletedZeta) (rho : ℂ),
    FunctionalEquation xi → IsZero xi rho → IsZero xi (1 - rho)

end MillenniumSuite.BSDRH
