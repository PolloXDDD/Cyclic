import MillenniumSuite.RH_PNP.Theorem

/-!
# Exact combinatorial meaning of the SAT penalty

The recursive penalty from `Construction.lean` takes only the values `0` and
`1` on each clause. Consequently the formula penalty is exactly the number of
clauses whose clause penalty is nonzero. This is the discrete content behind
the manuscript's clause-penalty polynomial before any spectral/QMC step.
-/

set_option autoImplicit false

namespace MillenniumSuite.RHPNP

/-- Every literal penalty is an indicator: it is either zero or one. -/
theorem literalPenalty_zero_or_one {n : Nat}
    (a : Assignment n) (lit : Literal n) :
    literalPenalty a lit = 0 ∨ literalPenalty a lit = 1 := by
  unfold literalPenalty
  split <;> simp_all

/-- Every clause penalty is an indicator: it is either zero or one. -/
theorem clausePenalty_zero_or_one {n : Nat}
    (a : Assignment n) (C : Clause n) :
    clausePenalty a C = 0 ∨ clausePenalty a C = 1 := by
  induction C with
  | nil =>
      exact Or.inr rfl
  | cons lit C ih =>
      rcases literalPenalty_zero_or_one a lit with hlit | hlit <;>
      rcases ih with htail | htail <;>
      simp [clausePenalty, hlit, htail]

/-- Executable count of clauses whose penalty indicator is nonzero. -/
def unsatisfiedClauseCount {n : Nat}
    (a : Assignment n) : CNF n → Nat
  | [] => 0
  | C :: F =>
      (if clausePenalty a C = 0 then 0 else 1) +
        unsatisfiedClauseCount a F

/-- The recursive formula penalty is exactly the number of unsatisfied clauses. -/
theorem formulaPenalty_eq_unsatisfiedClauseCount {n : Nat}
    (a : Assignment n) (F : CNF n) :
    formulaPenalty a F = unsatisfiedClauseCount a F := by
  induction F with
  | nil =>
      rfl
  | cons C F ih =>
      by_cases hzero : clausePenalty a C = 0
      · simp [formulaPenalty, unsatisfiedClauseCount, hzero, ih]
      · have hone : clausePenalty a C = 1 :=
          (clausePenalty_zero_or_one a C).resolve_left hzero
        simp [formulaPenalty, unsatisfiedClauseCount, hone, ih]

/-- The exact count never exceeds the number of clauses. -/
theorem unsatisfiedClauseCount_le_length {n : Nat}
    (a : Assignment n) (F : CNF n) :
    unsatisfiedClauseCount a F ≤ F.length := by
  induction F with
  | nil =>
      simp [unsatisfiedClauseCount]
  | cons C F ih =>
      by_cases hzero : clausePenalty a C = 0
      · simp [unsatisfiedClauseCount, hzero]
        exact Nat.le_succ_of_le ih
      · simp [unsatisfiedClauseCount, hzero]
        simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.succ_le_succ ih

/-- An assignment satisfies the formula iff its exact unsatisfied-clause count is zero. -/
theorem formulaSatisfied_iff_unsatisfiedClauseCount_eq_zero {n : Nat}
    (a : Assignment n) (F : CNF n) :
    FormulaSatisfied a F ↔ unsatisfiedClauseCount a F = 0 := by
  rw [← formulaPenalty_eq_unsatisfiedClauseCount a F]
  exact (formulaPenalty_eq_zero_iff a F).symm

#print axioms MillenniumSuite.RHPNP.formulaPenalty_eq_unsatisfiedClauseCount
#print axioms MillenniumSuite.RHPNP.unsatisfiedClauseCount_le_length
#print axioms MillenniumSuite.RHPNP.formulaSatisfied_iff_unsatisfiedClauseCount_eq_zero

end MillenniumSuite.RHPNP
