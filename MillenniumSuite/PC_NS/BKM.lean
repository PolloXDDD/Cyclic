import MillenniumSuite.PC_NS.ProblemStatement

/-!
# PC -> NS: BKM integration layer

This module starts the continuation side of the first bridge. At this stage we
prove only general integration facts already available from Mathlib; the
PDE-specific Beale--Kato--Majda continuation theorem remains a later module.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace MillenniumSuite.PCNS

/-- Any continuous real-valued vorticity-sup profile is integrable on every
compact time interval. -/
theorem continuous_profile_bkm_finite
    (omegaSup : VorticitySupProfile) (hOmega : Continuous omegaSup) (T : ℝ) :
    BKMFinite T omegaSup := by
  exact hOmega.intervalIntegrable 0 T

#print axioms MillenniumSuite.PCNS.continuous_profile_bkm_finite

end MillenniumSuite.PCNS
