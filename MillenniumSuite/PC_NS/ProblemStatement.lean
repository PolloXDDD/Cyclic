import Mathlib

/-!
# PC -> NS: source-level problem statement

This module contains definitions only. In the same style as
`openai/NavierStokesAndEuler`, introducing the target propositions does not
assert that they are true.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff EuclideanGeometry

universe u

namespace MillenniumSuite.PCNS

/-- Ambient Euclidean four-space in which the round unit 3-sphere lives. -/
abbrev Ambient4 := EuclideanSpace ℝ (Fin 4)

/-- The Euclidean three-space used as the local model for 3-manifolds. -/
abbrev Model3 := EuclideanSpace ℝ (Fin 3)

/-- The unit round 3-sphere, matching the geometric normal form used in the paper. -/
def Sphere3 : Set Ambient4 := Metric.sphere (0 : Ambient4) 1

/-- Points of the unit round 3-sphere. -/
abbrev Sphere3Point := {x : Ambient4 // x ∈ Sphere3}

/-- Smooth three-dimensional Poincare statement used as the antecedent of the
first transduction. The homotopy-equivalence type is written explicitly rather
than through scoped notation so the file is parser-independent. -/
def PoincareStatement : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace Model3 M]
      [IsManifold (𝓡 3) ∞ M],
    ContinuousMap.HomotopyEquiv M Sphere3Point →
      Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3Point)

/-- The three scalar functions that occur in the vorticity/enstrophy balance. -/
structure EnstrophyTrajectory where
  energy : ℝ → ℝ
  dissipation : ℝ → ℝ
  stretching : ℝ → ℝ

/-- Exact differential form of the manuscript's enstrophy identity. -/
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

/-- The next source-level target after the local differential estimate. -/
def UniformEnstrophyTarget (T : ℝ) (q : EnstrophyTrajectory) : Prop :=
  ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Ico (0 : ℝ) T, q.energy t ≤ M

/-- A scalar profile for the BKM vorticity norm. -/
abbrev VorticitySupProfile := ℝ → ℝ

/-- Finite BKM integral on `[0,T]`. -/
def BKMFinite (T : ℝ) (omegaSup : VorticitySupProfile) : Prop :=
  IntervalIntegrable omegaSup MeasureTheory.volume 0 T

end MillenniumSuite.PCNS
