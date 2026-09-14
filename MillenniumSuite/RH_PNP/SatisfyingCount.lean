import MillenniumSuite.RH_PNP.Theorem
import MillenniumSuite.RH_PNP.QMCThreshold
import Mathlib.Tactic

namespace MillenniumSuite.RHPNP

open Finset

/-- The finite set of satisfying Boolean assignments of a CNF formula. -/
noncomputable def satisfyingAssignments {n : Nat} (F : CNF n) : Finset (Assignment n) := by
  classical
  exact Finset.univ.filter (fun a => FormulaSatisfied a F)

/-- Exact number of satisfying assignments. -/
noncomputable def satisfyingCount {n : Nat} (F : CNF n) : Nat :=
  (satisfyingAssignments F).card

@[simp] theorem mem_satisfyingAssignments {n : Nat}
    (F : CNF n) (a : Assignment n) :
    a ∈ satisfyingAssignments F ↔ FormulaSatisfied a F := by
  classical
  simp [satisfyingAssignments]

/-- A formula is satisfiable iff its exact satisfying-assignment count is positive. -/
theorem satisfiable_iff_satisfyingCount_pos {n : Nat} (F : CNF n) :
    Satisfiable F ↔ 0 < satisfyingCount F := by
  classical
  rw [Nat.lt_iff_add_one_le, Nat.add_zero]
  constructor
  · rintro ⟨a, ha⟩
    unfold satisfyingCount
    have hmem : a ∈ satisfyingAssignments F := (mem_satisfyingAssignments F a).2 ha
    exact Finset.card_pos.mpr ⟨a, hmem⟩
  · intro hpos
    unfold satisfyingCount at hpos
    rcases Finset.card_pos.mp hpos with ⟨a, ha⟩
    exact ⟨a, (mem_satisfyingAssignments F a).1 ha⟩

/-- An unsatisfiable formula has exact count zero. -/
theorem not_satisfiable_iff_satisfyingCount_eq_zero {n : Nat} (F : CNF n) :
    ¬ Satisfiable F ↔ satisfyingCount F = 0 := by
  rw [satisfiable_iff_satisfyingCount_pos]
  omega

/-- The manuscript's `3/4` rule is exact once the analytic approximation is
known to be within `1/4` of the true integer count. -/
theorem satisfiable_iff_approximation_above_three_quarters
    {n : Nat} (F : CNF n) (I : ℝ)
    (happrox : ApproxWithinQuarter (satisfyingCount F) I) :
    Satisfiable F ↔ (3 : ℝ) / 4 < I := by
  constructor
  · intro hsat
    have hpos : 0 < satisfyingCount F :=
      (satisfiable_iff_satisfyingCount_pos F).1 hsat
    have hone : 1 ≤ satisfyingCount F := hpos
    exact positive_count_above_three_quarters hone happrox
  · intro hI
    by_contra hsat
    have hzero : satisfyingCount F = 0 :=
      (not_satisfiable_iff_satisfyingCount_eq_zero F).1 hsat
    have hbelow : I < (1 : ℝ) / 4 := by
      subst hzero
      exact zero_count_below_quarter happrox
    linarith

#print axioms MillenniumSuite.RHPNP.satisfiable_iff_satisfyingCount_pos
#print axioms MillenniumSuite.RHPNP.satisfiable_iff_approximation_above_three_quarters

end MillenniumSuite.RHPNP
