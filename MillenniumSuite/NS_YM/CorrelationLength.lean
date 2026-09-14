import MillenniumSuite.NS_YM.ProblemStatement

namespace MillenniumSuite.NSYM

/-- The final numerical implication in the manuscript is completely elementary
once the analytic construction has produced a positive correlation length and
the identity `delta = xi⁻¹`. -/
theorem correlation_implies_positive_mass_gap : CorrelationToMassGap := by
  intro d h
  rcases h with ⟨hxi, heta, hdelta, hxieta⟩
  unfold PositiveMassGap
  rw [hdelta]
  exact inv_pos.mpr hxi

/-- The dissipative length itself also has a positive inverse. -/
theorem dissipative_inverse_positive {d : CorrelationData}
    (h : CorrelationHypotheses d) : 0 < d.eta⁻¹ := by
  exact inv_pos.mpr h.2.1

/-- The exact quantitative inequality displayed in the paper:
`xi ≤ eta` implies `eta⁻¹ ≤ delta = xi⁻¹`. -/
theorem mass_gap_ge_dissipative_inverse {d : CorrelationData}
    (h : CorrelationHypotheses d) :
    d.eta⁻¹ ≤ d.delta := by
  rcases h with ⟨hxi, heta, hdelta, hxieta⟩
  rw [hdelta]
  exact (inv_le_inv₀ heta hxi).2 hxieta

/-- Combined form `0 < eta⁻¹ ≤ delta`. -/
theorem positive_dissipative_inverse_le_mass_gap {d : CorrelationData}
    (h : CorrelationHypotheses d) :
    0 < d.eta⁻¹ ∧ d.eta⁻¹ ≤ d.delta :=
  ⟨dissipative_inverse_positive h, mass_gap_ge_dissipative_inverse h⟩

#print axioms MillenniumSuite.NSYM.correlation_implies_positive_mass_gap
#print axioms MillenniumSuite.NSYM.dissipative_inverse_positive
#print axioms MillenniumSuite.NSYM.mass_gap_ge_dissipative_inverse

end MillenniumSuite.NSYM
