import MillenniumSuite.PC_NS.ProblemStatement

/-!
# PC -> NS: enstrophy differential estimate

This module formalizes the inference from the manuscript's exact enstrophy
balance to the post-Young differential inequality.  It contains no postulated
analytic theorem and no proof-carrying certificate structure.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace MillenniumSuite.PCNS

/-- A real number is bounded above by its absolute value.  Kept as a named
local lemma because it is exactly the sign step used on the stretching term. -/
theorem stretching_le_abs (S : ℝ) : S ≤ |S| := by
  exact le_abs_self S

/-- Equations (3.1)--(3.2) of the manuscript imply the displayed scalar
differential inequality pointwise on the lifespan.

The derivative witness is the one supplied by the exact balance; only ordered
ring arithmetic is used after that. -/
theorem enstrophy_differential_bound
    {ν K Cν CK E0 T : ℝ} {q : EnstrophyTrajectory}
    (hbalance : EnstrophyBalance ν K T q)
    (hstretch : StretchingBound ν Cν CK E0 T q)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    ∃ E' : ℝ,
      HasDerivAt q.energy E' t ∧
      E' ≤
        -ν * q.dissipation t - 4 * ν * K * q.energy t +
        2 * Cν * (q.energy t) ^ 3 +
        2 * CK * E0 * q.energy t := by
  let E' : ℝ :=
    2 * (q.stretching t - ν * q.dissipation t - 2 * ν * K * q.energy t)
  refine ⟨E', hbalance t ht, ?_⟩
  have hSabs : q.stretching t ≤ |q.stretching t| :=
    stretching_le_abs (q.stretching t)
  have hS := hstretch t ht
  dsimp [E']
  nlinarith

/-- The positive-curvature contribution is genuinely dissipative whenever
viscosity, curvature, and enstrophy are nonnegative. -/
theorem ricci_damping_nonpositive
    {ν K E : ℝ} (hν : 0 ≤ ν) (hK : 0 ≤ K) (hE : 0 ≤ E) :
    -4 * ν * K * E ≤ 0 := by
  have hprod : 0 ≤ ν * K * E := mul_nonneg (mul_nonneg hν hK) hE
  nlinarith

/-- Under the physical sign conditions, the dissipation term is also
nonpositive. -/
theorem viscous_dissipation_nonpositive
    {ν D : ℝ} (hν : 0 ≤ ν) (hD : 0 ≤ D) : -ν * D ≤ 0 := by
  have hprod : 0 ≤ ν * D := mul_nonneg hν hD
  nlinarith

/-- A convenience corollary exposing both damping signs directly from the
`PhysicalEnstrophySigns` predicate. -/
theorem physical_damping_signs
    {ν K T : ℝ} {q : EnstrophyTrajectory}
    (hsigns : PhysicalEnstrophySigns ν K T q)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    -ν * q.dissipation t ≤ 0 ∧ -4 * ν * K * q.energy t ≤ 0 := by
  rcases hsigns with ⟨hν, hK, _hT, hnonneg⟩
  have hq := hnonneg t ht
  constructor
  · exact viscous_dissipation_nonpositive hν.le hq.2
  · exact ricci_damping_nonpositive hν.le hK.le hq.1

end MillenniumSuite.PCNS

namespace MillenniumSuite.PCNS

/-- If the cubic term is below the curvature scale at a given time, it can be
absorbed into half of the Ricci damping.  This is a purely quantitative lemma;
it introduces no new analytic hypothesis beyond the displayed threshold. -/
theorem cubic_absorbed_by_ricci
    {ν K Cν E : ℝ}
    (hE : 0 ≤ E)
    (hthreshold : Cν * E ^ 2 ≤ ν * K) :
    2 * Cν * E ^ 3 ≤ 2 * ν * K * E := by
  have h2E : 0 ≤ 2 * E := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hthreshold h2E
  nlinarith

/-- Pointwise refinement of `enstrophy_differential_bound` in the regime where
the cubic term is absorbable by the positive-curvature damping. -/
theorem enstrophy_differential_bound_under_curvature_threshold
    {ν K Cν CK E0 T : ℝ} {q : EnstrophyTrajectory}
    (hbalance : EnstrophyBalance ν K T q)
    (hstretch : StretchingBound ν Cν CK E0 T q)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hE : 0 ≤ q.energy t)
    (hthreshold : Cν * (q.energy t) ^ 2 ≤ ν * K) :
    ∃ E' : ℝ,
      HasDerivAt q.energy E' t ∧
      E' ≤
        -ν * q.dissipation t +
        2 * (CK * E0 - ν * K) * q.energy t := by
  obtain ⟨E', hderiv, hbound⟩ :=
    enstrophy_differential_bound hbalance hstretch ht
  have habsorb :
      2 * Cν * (q.energy t) ^ 3 ≤ 2 * ν * K * q.energy t :=
    cubic_absorbed_by_ricci hE hthreshold
  refine ⟨E', hderiv, ?_⟩
  nlinarith

end MillenniumSuite.PCNS
