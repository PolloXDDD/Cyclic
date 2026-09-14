import MillenniumSuite.RH_PNP.Construction

/-!
# Correctness theorem for the explicit SAT penalty

This is the OpenAI-style endpoint for this slice: the target is discharged by
an explicit construction, with no proof certificate supplied as an argument.
-/

set_option autoImplicit false

namespace MillenniumSuite.RHPNP

@[simp] theorem literalPenalty_eq_zero_iff {n : Nat}
    (a : Assignment n) (lit : Literal n) :
    literalPenalty a lit = 0 ↔ Literal.eval a lit = true := by
  simp [literalPenalty]

@[simp] theorem clausePenalty_eq_zero_iff {n : Nat}
    (a : Assignment n) (C : Clause n) :
    clausePenalty a C = 0 ↔ ClauseSatisfied a C := by
  induction C with
  | nil =>
      simp [clausePenalty, ClauseSatisfied]
  | cons lit C ih =>
      by_cases h : Literal.eval a lit = true
      · simp [clausePenalty, ClauseSatisfied, literalPenalty, h]
      · simpa [clausePenalty, ClauseSatisfied, literalPenalty, h] using ih

@[simp] theorem formulaPenalty_eq_zero_iff {n : Nat}
    (a : Assignment n) (F : CNF n) :
    formulaPenalty a F = 0 ↔ FormulaSatisfied a F := by
  induction F with
  | nil =>
      simp [formulaPenalty, FormulaSatisfied]
  | cons C F ih =>
      simp [formulaPenalty, FormulaSatisfied, ih]

/-- Exact existential equivalence between SAT and zero global penalty. -/
theorem satisfiable_iff_exists_zero_penalty {n : Nat} (F : CNF n) :
    Satisfiable F ↔ ∃ a : Assignment n, formulaPenalty a F = 0 := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (formulaPenalty_eq_zero_iff a F).2 ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, (formulaPenalty_eq_zero_iff a F).1 ha⟩

/-- The statement module's target is proved by the concrete recursive penalty. -/
theorem zeroPenaltyEncoding : ZeroPenaltyEncodingStatement := by
  refine ⟨fun {n} a F => formulaPenalty a F, ?_⟩
  intro n F
  exact satisfiable_iff_exists_zero_penalty F

end MillenniumSuite.RHPNP
