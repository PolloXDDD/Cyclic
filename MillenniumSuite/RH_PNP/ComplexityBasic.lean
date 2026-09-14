import MillenniumSuite.RH_PNP.ComplexityStatement

universe u

namespace MillenniumSuite.RHPNP

/-- Every deterministic polynomial-time decider is an NP verifier that ignores
its witness.  The witness can be the empty string. -/
theorem p_subset_np (M : MachineModel) (L : Language) :
    InP M L → InNP M L := by
  rintro ⟨d, hcorrect, ⟨c, k, hcost⟩⟩
  refine ⟨M.lift d, ?_, ?_⟩
  · refine ⟨1, 0, ?_⟩
    intro x
    constructor
    · intro hx
      refine ⟨[], by simp, ?_⟩
      rw [M.lift_run d x []]
      exact (hcorrect x).2 hx
    · rintro ⟨w, _, hverify⟩
      have hrun : M.run d x = true := by
        rw [← M.lift_run d x w]
        exact hverify
      exact (hcorrect x).1 hrun
  · refine ⟨c, k, ?_⟩
    intro x w
    exact (M.lift_cost d x w).trans (hcost x)

/-- Under `P = NP`, every NP language has a polynomial-time decider. -/
theorem inP_of_pEqualsNP (M : MachineModel) (L : Language)
    (hEq : PEqualsNP M) (hNP : InNP M L) : InP M L := by
  exact (hEq L).mpr hNP

/-- Since `P ⊆ NP` is formalized above, class equality is equivalent to the
reverse inclusion. -/
theorem pEqualsNP_iff_np_subset_p (M : MachineModel) :
    PEqualsNP M ↔ ∀ L : Language, InNP M L → InP M L := by
  constructor
  · intro hEq L hNP
    exact inP_of_pEqualsNP M L hEq hNP
  · intro hrev L
    constructor
    · exact p_subset_np M L
    · exact hrev L

#print axioms MillenniumSuite.RHPNP.p_subset_np
#print axioms MillenniumSuite.RHPNP.pEqualsNP_iff_np_subset_p

end MillenniumSuite.RHPNP
