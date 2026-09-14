import MillenniumSuite.PC_NS.ProblemStatement

/-!
# PC -> NS: round-sphere geometry layer
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
  rw [← dist_zero_right]
  exact sphere3_radius x

/-- Direct elimination rule for the Poincare antecedent. -/
theorem smooth_equiv_sphere_of_poincare
    (hPC : PoincareStatement.{u})
    (M : Type u) [TopologicalSpace M] [T2Space M] [ChartedSpace Model3 M]
    [IsManifold (𝓡 3) ∞ M]
    (hM : ContinuousMap.HomotopyEquiv M Sphere3Point) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3Point) := by
  exact hPC M hM

#print axioms MillenniumSuite.PCNS.sphere3_norm
#print axioms MillenniumSuite.PCNS.smooth_equiv_sphere_of_poincare

end MillenniumSuite.PCNS
