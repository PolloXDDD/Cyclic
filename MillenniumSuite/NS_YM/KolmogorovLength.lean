import MillenniumSuite.NS_YM.CorrelationLength
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace MillenniumSuite.NSYM

/-- Kolmogorov dissipative length `eta = (nu^3 / epsilon)^(1/4)`. -/
def kolmogorovLength (nu epsilon : ℝ) : ℝ :=
  (nu ^ 3 / epsilon) ^ ((1 : ℝ) / 4)

/-- Positive viscosity and positive dissipation rate give a positive dissipative length. -/
theorem kolmogorovLength_pos {nu epsilon : ℝ}
    (hnu : 0 < nu) (hepsilon : 0 < epsilon) :
    0 < kolmogorovLength nu epsilon := by
  unfold kolmogorovLength
  apply Real.rpow_pos_of_pos
  exact div_pos (pow_pos hnu 3) hepsilon

/-- The inverse dissipative scale is therefore strictly positive. -/
theorem kolmogorovLength_inv_pos {nu epsilon : ℝ}
    (hnu : 0 < nu) (hepsilon : 0 < epsilon) :
    0 < (kolmogorovLength nu epsilon)⁻¹ := by
  exact inv_pos.mpr (kolmogorovLength_pos hnu hepsilon)

/-- Assemble the numerical correlation data used by the mass-gap endpoint. -/
def correlationDataFromKolmogorov (nu epsilon xi : ℝ) : CorrelationData where
  xi := xi
  eta := kolmogorovLength nu epsilon
  delta := xi⁻¹

/-- If the vacuum correlation length is controlled by the Kolmogorov scale, all
numerical hypotheses of the mass-gap lemma follow from positive physical data. -/
theorem correlationHypotheses_from_kolmogorov
    {nu epsilon xi : ℝ}
    (hnu : 0 < nu) (hepsilon : 0 < epsilon)
    (hxi : 0 < xi)
    (hcontrol : xi ≤ kolmogorovLength nu epsilon) :
    CorrelationHypotheses (correlationDataFromKolmogorov nu epsilon xi) := by
  exact ⟨hxi, kolmogorovLength_pos hnu hepsilon, rfl, hcontrol⟩

/-- Direct numerical endpoint: the constructed data have a positive mass gap. -/
theorem positive_mass_gap_from_kolmogorov_control
    {nu epsilon xi : ℝ}
    (hnu : 0 < nu) (hepsilon : 0 < epsilon)
    (hxi : 0 < xi)
    (hcontrol : xi ≤ kolmogorovLength nu epsilon) :
    PositiveMassGap (correlationDataFromKolmogorov nu epsilon xi) := by
  exact correlation_implies_positive_mass_gap _
    (correlationHypotheses_from_kolmogorov hnu hepsilon hxi hcontrol)

#print axioms MillenniumSuite.NSYM.positive_mass_gap_from_kolmogorov_control

end MillenniumSuite.NSYM
