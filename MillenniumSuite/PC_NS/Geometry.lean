import MillenniumSuite.PC_NS.ProblemStatement

/-!
# PC -> NS: round-sphere geometry layer

The purpose of this module is deliberately narrow: establish concrete facts
about the exact sphere used by the first transduction, without packaging them
as assumptions or certificates.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff EuclideanGeometry

universe u

namespace MillenniumSuite.PCNS

/-- Membership in `Sphere3Point` is literally the unit-radius equation. -/
theorem sphere3_radius (x : Sphere3Point) :
    dist (x : Ambient4) (0 : Ambient4) = 1 := by
  change (x : Ambient4) ∈ Metric.sphere (0 : Ambient4) 1
  exact x.property

/-- Hence every point of the chosen round 3-sphere has Euclidean norm one. -/
theorem sphere3_norm (x : Sphere3Point) : ‖(x : Ambient4)‖ = 1 := by
  have hx := sphere3_radius x
  simpa [dist_eq_norm] using hx

/-- Direct elimination rule for the Poincare antecedent: once an explicit
homotopy equivalence with the unit 3-sphere is supplied, the statement gives a
smooth equivalence.  No additional bridge hypothesis is introduced. -/
theorem smooth_equiv_sphere_of_poincare
    (hPC : PoincareStatement)
    (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace (ℝ^3) M]
    [IsManifold (𝓡 3) ∞ M]
    (hM : M ≃ₕ Sphere3Point) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3Point) := by
  exact hPC M hM

end MillenniumSuite.PCNS
