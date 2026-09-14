import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# NS -> YM: correlation-length / mass-gap layer

This module isolates the quantitative end of Transduction II in the manuscript.
It does not assume the bridge theorem.  It only defines the numerical data and
the hypotheses that the preceding analytic/gauge-theoretic construction must
supply.
-/

noncomputable section

namespace MillenniumSuite.NSYM

/-- Numerical quantities appearing at the end of the NS -> YM argument. -/
structure CorrelationData where
  xi : ℝ
  eta : ℝ
  delta : ℝ

/-- The manuscript's correlation-length hypotheses:
`xi > 0`, `eta > 0`, `delta = xi⁻¹`, and `xi ≤ eta`. -/
def CorrelationHypotheses (d : CorrelationData) : Prop :=
  0 < d.xi ∧ 0 < d.eta ∧ d.delta = d.xi⁻¹ ∧ d.xi ≤ d.eta

/-- Strict positivity of the Yang--Mills mass gap. -/
def PositiveMassGap (d : CorrelationData) : Prop :=
  0 < d.delta

/-- Target of the quantitative correlation-length subargument. -/
def CorrelationToMassGap : Prop :=
  ∀ d : CorrelationData, CorrelationHypotheses d → PositiveMassGap d

end MillenniumSuite.NSYM
