import Mathlib

/-!
# Vector-valued Hermitian--Einstein residuals

This module upgrades the scalar energy bookkeeping to actual elements of normed
spaces representing `F_A^{0,2}` and `Lambda F_A - c Id`.
-/

noncomputable section

namespace MillenniumSuite.YMHodge

structure HEData (V W : Type*) [NormedAddCommGroup V] [NormedAddCommGroup W] where
  action : ℝ
  topological : ℝ
  curvature02 : V
  momentResidual : W

/-- The Yang--Mills decomposition from the manuscript. -/
def HEEnergyIdentity {V W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    (d : HEData V W) : Prop :=
  d.action = d.topological + 2 * ‖d.curvature02‖ ^ 2 + ‖d.momentResidual‖ ^ 2

/-- Absolute minimality of the action. -/
def HEAtMinimum {V W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    (d : HEData V W) : Prop :=
  d.action = d.topological

/-- At the topological minimum both geometric residual fields vanish. -/
theorem he_residual_fields_vanish {V W : Type*}
    [NormedAddCommGroup V] [NormedAddCommGroup W]
    (d : HEData V W) (hE : HEEnergyIdentity d) (hmin : HEAtMinimum d) :
    d.curvature02 = 0 ∧ d.momentResidual = 0 := by
  unfold HEEnergyIdentity HEAtMinimum at hE hmin
  have hsum : 2 * ‖d.curvature02‖ ^ 2 + ‖d.momentResidual‖ ^ 2 = 0 := by
    nlinarith
  have hc_nonneg : 0 ≤ ‖d.curvature02‖ := norm_nonneg _
  have hm_nonneg : 0 ≤ ‖d.momentResidual‖ := norm_nonneg _
  have hc : ‖d.curvature02‖ = 0 := by
    nlinarith [sq_nonneg ‖d.curvature02‖, sq_nonneg ‖d.momentResidual‖]
  have hm : ‖d.momentResidual‖ = 0 := by
    nlinarith [sq_nonneg ‖d.curvature02‖, sq_nonneg ‖d.momentResidual‖]
  exact ⟨norm_eq_zero.mp hc, norm_eq_zero.mp hm⟩

#print axioms MillenniumSuite.YMHodge.he_residual_fields_vanish

end MillenniumSuite.YMHodge
