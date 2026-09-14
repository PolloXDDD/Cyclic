import Mathlib

/-!
# PC -> NS: source-level problem statement

This module contains definitions only.  In the same style as
`openai/NavierStokesAndEuler`, introducing the target propositions does not
assert that they are true.

The Poincare node is stated in the smooth three-dimensional form used by the
manuscript: a smooth 3-manifold homotopy equivalent to the unit 3-sphere is
smoothly equivalent to that sphere.

For the analytic part of the first transduction we isolate the exact scalar
quantities appearing in the manuscript's enstrophy identity.  Later modules
will construct these quantities from an actual Navier--Stokes solution.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff EuclideanGeometry

universe u

namespace MillenniumSuite.PCNS

/-- Ambient Euclidean four-space in which the round unit 3-sphere lives. -/
abbrev Ambient4 := EuclideanSpace ℝ (Fin 4)

/-- The unit round 3-sphere, matching the geometric normal form used in the paper. -/
def Sphere3 : Set Ambient4 := Metric.sphere (0 : Ambient4) 1

/-- Points of the unit round 3-sphere. -/
abbrev Sphere3Point := {x : Ambient4 // x ∈ Sphere3}

/-- Smooth three-dimensional Poincare statement used as the antecedent of the
first transduction.  It is a proposition, not an axiom and not a theorem here. -/
def PoincareStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
      [IsManifold (𝓡 3) ∞ M],
    (M ≃ₕ Sphere3Point) → Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3Point)

/-- The three scalar functions that occur in the vorticity/enstrophy balance:
`energy = ||omega||_2^2`, `dissipation = ||nabla omega||_2^2`, and the
vortex-stretching integral.  This record contains data only, no proof fields. -/
structure EnstrophyTrajectory where
  energy : ℝ → ℝ
  dissipation : ℝ → ℝ
  stretching : ℝ → ℝ

/-- Exact differential form of manuscript equation (3.1):

`1/2 E' + nu D + 2 nu K E = S`.

Writing it as the derivative formula avoids introducing a symbolic derivative
operator separate from Mathlib's `HasDerivAt`. -/
def EnstrophyBalance (ν K T : ℝ) (q : EnstrophyTrajectory) : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) T,
    HasDerivAt q.energy
      (2 * (q.stretching t - ν * q.dissipation t - 2 * ν * K * q.energy t)) t

/-- Manuscript vortex-stretching estimate after Young's inequality. -/
def StretchingBound (ν Cν CK E0 T : ℝ) (q : EnstrophyTrajectory) : Prop :=
  ∀ t ∈ Ioo (0 : ℝ) T,
    |q.stretching t| ≤
      (ν / 2) * q.dissipation t +
      Cν * (q.energy t) ^ 3 +
      CK * E0 * q.energy t

/-- Positivity/nonnegativity properties satisfied by the physical quantities. -/
def PhysicalEnstrophySigns (ν K T : ℝ) (q : EnstrophyTrajectory) : Prop :=
  0 < ν ∧ 0 < K ∧ 0 < T ∧
    ∀ t ∈ Ioo (0 : ℝ) T, 0 ≤ q.energy t ∧ 0 ≤ q.dissipation t

/-- The next source-level target after the local differential estimate: the
uniform finite-time enstrophy bound stated in the manuscript.  This remains a
target proposition until its construction/estimate modules discharge it. -/
def UniformEnstrophyTarget (T : ℝ) (q : EnstrophyTrajectory) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Ico (0 : ℝ) T, q.energy t ≤ M

/-- A scalar profile for the BKM vorticity norm `||omega(t)||_infinity`. -/
abbrev VorticitySupProfile := ℝ → ℝ

/-- Finite BKM integral on `[0,T]`. -/
def BKMFinite (T : ℝ) (ω∞ : VorticitySupProfile) : Prop :=
  IntervalIntegrable ω∞ MeasureTheory.volume 0 T

end MillenniumSuite.PCNS
