import Mathlib

/-!
# Rational closure of algebraic cycle classes

At the endpoint of the manuscript's YM -> Hodge route, a rational Hodge class
is expressed as a finite rational linear combination of algebraic cycle classes.
Algebraic classes are therefore modeled here as a `ℚ`-submodule of cohomology,
and the closure under the displayed finite sum is proved directly.
-/

namespace MillenniumSuite.YMHodge

/-- Finite rational combinations of algebraic classes remain algebraic. -/
theorem rational_linear_combination_mem
    {H : Type*} [AddCommGroup H] [Module ℚ H]
    (A : Submodule ℚ H)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℚ) (z : ι → H)
    (hz : ∀ i, z i ∈ A) :
    (∑ i, q i • z i) ∈ A := by
  apply Submodule.sum_mem
  intro i hi
  exact A.smul_mem (q i) (hz i)

/-- In particular, if a Hodge class equals such a combination, then it lies in
 the algebraic submodule. -/
theorem class_mem_of_eq_rational_cycle_sum
    {H : Type*} [AddCommGroup H] [Module ℚ H]
    (A : Submodule ℚ H)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (alpha : H) (q : ι → ℚ) (z : ι → H)
    (hz : ∀ i, z i ∈ A)
    (hrep : alpha = ∑ i, q i • z i) :
    alpha ∈ A := by
  rw [hrep]
  exact rational_linear_combination_mem A q z hz

#print axioms MillenniumSuite.YMHodge.rational_linear_combination_mem
#print axioms MillenniumSuite.YMHodge.class_mem_of_eq_rational_cycle_sum

end MillenniumSuite.YMHodge
