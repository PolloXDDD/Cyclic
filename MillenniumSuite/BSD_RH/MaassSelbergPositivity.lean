import MillenniumSuite.BSD_RH.CriticalLine
import Mathlib.Tactic

/-!
# Positivity contradiction in the BSD -> RH transduction

The manuscript's last analytic step compares a nonnegative Hilbert-space norm
with the residue expression

`- |Res Phi(s0)|^2 / (2 sigma - 1)`.

For `sigma > 1/2` and a nonzero residue, that expression is strictly negative.
This module closes that real-algebraic contradiction independently of the
spectral argument that must produce the displayed residue identity.
-/

noncomputable section

namespace MillenniumSuite.BSDRH

/-- Real scalar form of the residue contribution appearing in the paper. -/
def residueTerm (R sigma : ℝ) : ℝ :=
  -(R ^ 2) / (2 * sigma - 1)

/-- A nonzero residue to the right of the critical line produces a strictly negative term. -/
theorem residue_term_negative {R sigma : ℝ}
    (hR : R ≠ 0) (hsigma : (1 : ℝ) / 2 < sigma) :
    residueTerm R sigma < 0 := by
  unfold residueTerm
  have hden : 0 < 2 * sigma - 1 := by
    linarith
  have hsq : 0 < R ^ 2 := sq_pos_of_ne_zero hR
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hsq) hden

/-- A nonnegative squared norm cannot equal the negative off-critical residue term. -/
theorem maass_selberg_positivity_contradiction
    {normSq R sigma : ℝ}
    (hnorm : 0 ≤ normSq)
    (hR : R ≠ 0)
    (hsigma : (1 : ℝ) / 2 < sigma)
    (heq : normSq = residueTerm R sigma) : False := by
  have hneg : residueTerm R sigma < 0 := residue_term_negative hR hsigma
  rw [heq] at hnorm
  exact (not_lt_of_ge hnorm) hneg

#print axioms MillenniumSuite.BSDRH.residue_term_negative
#print axioms MillenniumSuite.BSDRH.maass_selberg_positivity_contradiction

end MillenniumSuite.BSDRH
