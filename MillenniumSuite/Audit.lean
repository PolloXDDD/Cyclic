import MillenniumSuite.PC_NS
import MillenniumSuite.NS_YM
import MillenniumSuite.YM_Hodge
import MillenniumSuite.Hodge_BSD
import MillenniumSuite.BSD_RH
import MillenniumSuite.RH_PNP
import MillenniumSuite.PNP_PC

/-!
# Proof audit

As in `openai/NavierStokesAndEuler`, exported closed lemmas are inspected with
`#print axioms`. Open target propositions are definitions, not asserted facts.
-/

#print axioms MillenniumSuite.PCNS.sphere3_radius
#print axioms MillenniumSuite.PCNS.sphere3_norm
#print axioms MillenniumSuite.PCNS.smooth_equiv_sphere_of_poincare
#print axioms MillenniumSuite.PCNS.enstrophy_differential_bound
#print axioms MillenniumSuite.PCNS.ricci_damping_nonpositive
#print axioms MillenniumSuite.PCNS.viscous_dissipation_nonpositive
#print axioms MillenniumSuite.PCNS.physical_damping_signs
#print axioms MillenniumSuite.PCNS.continuous_profile_bkm_finite
#print axioms MillenniumSuite.PCNS.cubic_absorbed_by_ricci
#print axioms MillenniumSuite.PCNS.enstrophy_differential_bound_under_curvature_threshold

#print axioms MillenniumSuite.NSYM.curvature_swap
#print axioms MillenniumSuite.NSYM.curvature_self
#print axioms MillenniumSuite.NSYM.correlation_implies_positive_mass_gap
#print axioms MillenniumSuite.NSYM.dissipative_inverse_positive
#print axioms MillenniumSuite.NSYM.kolmogorovLength_pos
#print axioms MillenniumSuite.NSYM.kolmogorovLength_inv_pos
#print axioms MillenniumSuite.NSYM.correlationHypotheses_from_kolmogorov
#print axioms MillenniumSuite.NSYM.positive_mass_gap_from_kolmogorov_control

#print axioms MillenniumSuite.YMHodge.residual_square_sum_zero
#print axioms MillenniumSuite.YMHodge.minimum_forces_hermitian_einstein
#print axioms MillenniumSuite.YMHodge.he_residual_fields_vanish
#print axioms MillenniumSuite.YMHodge.rational_linear_combination_mem
#print axioms MillenniumSuite.YMHodge.class_mem_of_eq_rational_cycle_sum
#print axioms MillenniumSuite.YMHodge.algebraic_class_of_eq

#print axioms MillenniumSuite.HodgeBSD.bounds_give_rank_equality
#print axioms MillenniumSuite.HodgeBSD.arithmetic_bounds_give_bsd

#print axioms MillenniumSuite.BSDRH.functional_equation_zero_symmetry
#print axioms MillenniumSuite.BSDRH.zero_gives_scattering_denominator_zero
#print axioms MillenniumSuite.BSDRH.symmetric_zero_left_of_line
#print axioms MillenniumSuite.BSDRH.actual_completed_zeta_functional_equation
#print axioms MillenniumSuite.BSDRH.actual_completed_zeta_zero_symmetry
#print axioms MillenniumSuite.BSDRH.actual_zero_gives_scattering_denominator_zero
#print axioms MillenniumSuite.BSDRH.residue_term_negative
#print axioms MillenniumSuite.BSDRH.maass_selberg_positivity_contradiction

#print axioms MillenniumSuite.RHPNP.literalPenalty_eq_zero_iff
#print axioms MillenniumSuite.RHPNP.clausePenalty_eq_zero_iff
#print axioms MillenniumSuite.RHPNP.formulaPenalty_eq_zero_iff
#print axioms MillenniumSuite.RHPNP.satisfiable_iff_exists_zero_penalty
#print axioms MillenniumSuite.RHPNP.zeroPenaltyEncoding
#print axioms MillenniumSuite.RHPNP.p_subset_np
#print axioms MillenniumSuite.RHPNP.pEqualsNP_iff_np_subset_p
#print axioms MillenniumSuite.RHPNP.zero_count_below_quarter
#print axioms MillenniumSuite.RHPNP.positive_count_above_three_quarters
#print axioms MillenniumSuite.RHPNP.quarter_gap_separates_counts

#print axioms MillenniumSuite.PNPPC.PachnerReachable.trans
#print axioms MillenniumSuite.PNPPC.extend_sphere_certificate
#print axioms MillenniumSuite.PNPPC.reachable_iff_exists_finite_chain
#print axioms MillenniumSuite.PNPPC.sphere_recognition_inP_of_pEqualsNP
