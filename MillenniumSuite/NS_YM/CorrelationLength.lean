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

#print axioms MillenniumSuite.NSYM.correlation_implies_positive_mass_gap
#print axioms MillenniumSuite.NSYM.dissipative_inverse_positive

end MillenniumSuite.NSYM
