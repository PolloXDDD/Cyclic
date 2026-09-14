import MillenniumSuite.PNP_PC.FiniteCertificate

universe u

namespace MillenniumSuite.PNPPC

/-- Boolean checker for a concrete Pachner chain when elementary moves are decidable. -/
def verifyPachnerChain {K : Type u}
    [DecidableEq K] {step : K → K → Prop} [DecidableRel step]
    (a : K) (xs : List K) (b : K) : Bool :=
  decide (IsPachnerChain step a xs b)

/-- The Boolean checker is logically exact. -/
@[simp] theorem verifyPachnerChain_eq_true_iff {K : Type u}
    [DecidableEq K] {step : K → K → Prop} [DecidableRel step]
    (a : K) (xs : List K) (b : K) :
    verifyPachnerChain (step := step) a xs b = true ↔
      IsPachnerChain step a xs b := by
  simp [verifyPachnerChain]

/-- Sphere-certificate checker with the target standard triangulation fixed. -/
def verifySphereCertificate {K : Type u}
    [DecidableEq K] {step : K → K → Prop} [DecidableRel step]
    (standard input : K) (xs : List K) : Bool :=
  verifyPachnerChain (step := step) input xs standard

/-- Exact correctness of the finite sphere-certificate checker. -/
@[simp] theorem verifySphereCertificate_eq_true_iff {K : Type u}
    [DecidableEq K] {step : K → K → Prop} [DecidableRel step]
    (standard input : K) (xs : List K) :
    verifySphereCertificate (step := step) standard input xs = true ↔
      IsPachnerChain step input xs standard := by
  simp [verifySphereCertificate]

/-- Existence of an accepted finite certificate is equivalent to Pachner reachability. -/
theorem reachable_iff_exists_accepted_certificate {K : Type u}
    [DecidableEq K] {step : K → K → Prop} [DecidableRel step]
    {standard input : K} :
    HasSphereCertificate step standard input ↔
      ∃ xs : List K,
        verifySphereCertificate (step := step) standard input xs = true := by
  unfold HasSphereCertificate
  rw [reachable_iff_exists_finite_chain]
  simp

#print axioms MillenniumSuite.PNPPC.reachable_iff_exists_accepted_certificate

end MillenniumSuite.PNPPC
