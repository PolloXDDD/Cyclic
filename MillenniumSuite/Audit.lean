import MillenniumSuite.PC_NS
import MillenniumSuite.RH_PNP.Theorem

/-!
# Proof audit

As in `openai/NavierStokesAndEuler`, exported closed lemmas are inspected with
`#print axioms`.  Open target propositions are definitions, not asserted facts.
-/

#print axioms MillenniumSuite.PCNS.sphere3_radius
#print axioms MillenniumSuite.PCNS.sphere3_norm
#print axioms MillenniumSuite.PCNS.smooth_equiv_sphere_of_poincare
#print axioms MillenniumSuite.PCNS.enstrophy_differential_bound
#print axioms MillenniumSuite.PCNS.ricci_damping_nonpositive
#print axioms MillenniumSuite.PCNS.viscous_dissipation_nonpositive
#print axioms MillenniumSuite.PCNS.physical_damping_signs
#print axioms MillenniumSuite.PCNS.continuous_profile_bkm_finite

#print axioms MillenniumSuite.RHPNP.literalPenalty_eq_zero_iff
#print axioms MillenniumSuite.RHPNP.clausePenalty_eq_zero_iff
#print axioms MillenniumSuite.RHPNP.formulaPenalty_eq_zero_iff
#print axioms MillenniumSuite.RHPNP.satisfiable_iff_exists_zero_penalty
#print axioms MillenniumSuite.RHPNP.zeroPenaltyEncoding
#print axioms MillenniumSuite.PCNS.cubic_absorbed_by_ricci
#print axioms MillenniumSuite.PCNS.enstrophy_differential_bound_under_curvature_threshold
