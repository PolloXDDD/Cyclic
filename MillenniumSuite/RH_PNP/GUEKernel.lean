import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic

/-!
# GUE two-point kernel

The manuscript uses

`R₂(u) = 1 - (sin (πu) / (πu))²`.

Mathlib's continuous `Real.sinc` gives the canonical extension through `u = 0`,
so this module can define the kernel exactly and prove its elementary global
properties without assuming the GUE pair-correlation theorem itself.
-/

noncomputable section

namespace MillenniumSuite.RHPNP

/-- Continuous GUE pair-correlation kernel. -/
def gueKernel (u : ℝ) : ℝ :=
  1 - (Real.sinc (Real.pi * u)) ^ 2

/-- Level repulsion starts at zero separation. -/
@[simp] theorem gueKernel_zero : gueKernel 0 = 0 := by
  simp [gueKernel]

/-- The two-point kernel is even. -/
theorem gueKernel_neg (u : ℝ) : gueKernel (-u) = gueKernel u := by
  unfold gueKernel
  rw [mul_neg, Real.sinc_neg]

/-- The GUE kernel is nonnegative. -/
theorem gueKernel_nonneg (u : ℝ) : 0 ≤ gueKernel u := by
  have h := Real.abs_sinc_le_one (Real.pi * u)
  have hb := (abs_le.mp h)
  unfold gueKernel
  nlinarith

/-- The GUE kernel is bounded above by one. -/
theorem gueKernel_le_one (u : ℝ) : gueKernel u ≤ 1 := by
  unfold gueKernel
  nlinarith [sq_nonneg (Real.sinc (Real.pi * u))]

/-- Hence `R₂(u)` always lies in the probability-density range `[0,1]`. -/
theorem gueKernel_mem_unitInterval (u : ℝ) :
    gueKernel u ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨gueKernel_nonneg u, gueKernel_le_one u⟩

/-- The exact kernel is continuous on all of `ℝ`, including at the origin. -/
theorem continuous_gueKernel : Continuous gueKernel := by
  unfold gueKernel
  fun_prop

#print axioms MillenniumSuite.RHPNP.gueKernel_nonneg
#print axioms MillenniumSuite.RHPNP.continuous_gueKernel

end MillenniumSuite.RHPNP
