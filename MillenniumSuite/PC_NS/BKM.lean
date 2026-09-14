import MillenniumSuite.PC_NS.ProblemStatement

/-!
# PC -> NS: BKM integration layer

This module starts the continuation side of the first bridge.  At this stage we
prove only general integration facts that are already available from Mathlib;
the PDE-specific Beale--Kato--Majda continuation theorem will be a later module,
not an assumed field of a certificate.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace MillenniumSuite.PCNS

/-- Any continuous real-valued vorticity-sup profile is integrable on every
compact time interval. -/
theorem continuous_profile_bkm_finite
    (ω∞ : VorticitySupProfile) (hω : Continuous ω∞) (T : ℝ) :
    BKMFinite T ω∞ := by
  exact hω.intervalIntegrable 0 T

end MillenniumSuite.PCNS
