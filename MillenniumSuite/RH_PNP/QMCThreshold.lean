import Mathlib

/-!
# Quarter-gap decision threshold for the RH -> P=NP transduction

The manuscript concludes the quasi-Monte Carlo stage by requiring an approximation
error strictly below `1/4`.  Since the exact number of satisfying assignments is
an integer, this numerical gap alone is enough to separate zero from a positive
count by the thresholds `1/4` and `3/4`.
-/

namespace MillenniumSuite.RHPNP

/-- `I` approximates the exact nonnegative integer count to within a quarter. -/
def ApproxWithinQuarter (count : ℕ) (I : ℝ) : Prop :=
  |(count : ℝ) - I| < (1 : ℝ) / 4

/-- If the exact count is zero, every quarter-accurate approximation lies below `1/4`. -/
theorem zero_count_below_quarter {I : ℝ}
    (h : ApproxWithinQuarter 0 I) :
    I < (1 : ℝ) / 4 := by
  unfold ApproxWithinQuarter at h
  have h' : |I| < (1 : ℝ) / 4 := by
    simpa only [Nat.cast_zero, zero_sub, abs_neg] using h
  exact (abs_lt.mp h').2

/-- If the exact count is positive, every quarter-accurate approximation lies above `3/4`. -/
theorem positive_count_above_three_quarters {count : ℕ} {I : ℝ}
    (hcount : 1 ≤ count) (h : ApproxWithinQuarter count I) :
    (3 : ℝ) / 4 < I := by
  have hright : (count : ℝ) - I < (1 : ℝ) / 4 := (abs_lt.mp h).2
  have hcountR : (1 : ℝ) ≤ (count : ℝ) := by
    exact_mod_cast hcount
  linarith

/-- The `1/4` error guarantee gives a strict decision gap between UNSAT and SAT. -/
theorem quarter_gap_separates_counts (count : ℕ) (I : ℝ)
    (h : ApproxWithinQuarter count I) :
    (count = 0 → I < (1 : ℝ) / 4) ∧
    (1 ≤ count → (3 : ℝ) / 4 < I) := by
  constructor
  · intro hzero
    subst count
    exact zero_count_below_quarter h
  · intro hpos
    exact positive_count_above_three_quarters hpos h

#print axioms MillenniumSuite.RHPNP.quarter_gap_separates_counts

end MillenniumSuite.RHPNP
