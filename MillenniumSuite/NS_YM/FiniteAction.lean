import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite-action layer for NS -> YM

The manuscript passes from finite viscous dissipation / square-integrable
curvature to finiteness of the Euclidean Yang--Mills action.  This module
formalizes the measure-theoretic core: an `L²` real curvature profile has
integrable squared norm, and multiplying by the coupling prefactor preserves
integrability.
-/

noncomputable section

open MeasureTheory

namespace MillenniumSuite.NSYM

/-- Square-integrability gives integrability of the square. -/
theorem integrable_sq_of_memLp_two
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {F : X → ℝ}
    (hmeas : AEStronglyMeasurable F mu)
    (hL2 : MemLp F 2 mu) :
    Integrable (fun x => F x ^ 2) mu := by
  exact (memLp_two_iff_integrable_sq hmeas).mp hL2

/-- Scalar Yang--Mills action density with coupling `g`. -/
def actionDensity (g : ℝ) {X : Type*} (F : X → ℝ) (x : X) : ℝ :=
  (1 / (4 * g ^ 2)) * F x ^ 2

/-- An `L²` curvature profile has integrable Yang--Mills action density for any
real coupling.  Positivity of `g` is needed for the physical interpretation,
not for this integrability statement. -/
theorem integrable_actionDensity_of_memLp_two
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {F : X → ℝ} (g : ℝ)
    (hmeas : AEStronglyMeasurable F mu)
    (hL2 : MemLp F 2 mu) :
    Integrable (actionDensity g F) mu := by
  have hsq : Integrable (fun x => F x ^ 2) mu :=
    integrable_sq_of_memLp_two hmeas hL2
  simpa [actionDensity] using hsq.const_mul (1 / (4 * g ^ 2))

/-- The corresponding Euclidean action is an ordinary finite real integral. -/
def yangMillsAction
    {X : Type*} [MeasurableSpace X] (mu : Measure X)
    (g : ℝ) (F : X → ℝ) : ℝ :=
  ∫ x, actionDensity g F x ∂mu

#print axioms MillenniumSuite.NSYM.integrable_sq_of_memLp_two
#print axioms MillenniumSuite.NSYM.integrable_actionDensity_of_memLp_two

end MillenniumSuite.NSYM
