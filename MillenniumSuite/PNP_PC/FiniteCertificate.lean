import MillenniumSuite.PNP_PC.Pachner

universe u

namespace MillenniumSuite.PNPPC

/-- A concrete finite chain of elementary moves from `a` to `b`. -/
def IsPachnerChain {K : Type u} (step : K → K → Prop) : K → List K → K → Prop
  | a, [], b => a = b
  | a, c :: cs, b => step a c ∧ IsPachnerChain step c cs b

/-- Append one valid elementary move to the end of a concrete chain. -/
theorem chain_snoc {K : Type u} {step : K → K → Prop}
    {a b c : K} {xs : List K}
    (hchain : IsPachnerChain step a xs b)
    (hstep : step b c) :
    IsPachnerChain step a (xs ++ [c]) c := by
  induction xs generalizing a with
  | nil =>
      change a = b at hchain
      subst b
      change step a c ∧ c = c
      exact ⟨hstep, rfl⟩
  | cons x xs ih =>
      change step a x ∧ IsPachnerChain step x xs b at hchain
      change step a x ∧ IsPachnerChain step x (xs ++ [c]) c
      exact ⟨hchain.1, ih hchain.2 hstep⟩

/-- Every inductive Pachner-reachability proof yields an explicit finite move list. -/
theorem reachable_has_finite_chain {K : Type u} {step : K → K → Prop}
    {a b : K} (h : PachnerReachable step a b) :
    ∃ xs : List K, IsPachnerChain step a xs b := by
  induction h with
  | refl a =>
      exact ⟨[], rfl⟩
  | move hreach hstep ih =>
      rcases ih with ⟨xs, hxs⟩
      exact ⟨xs ++ [_], chain_snoc hxs hstep⟩

/-- Conversely, every explicit finite chain gives a Pachner-reachability proof. -/
theorem finite_chain_reachable {K : Type u} {step : K → K → Prop}
    {a b : K} {xs : List K}
    (hchain : IsPachnerChain step a xs b) :
    PachnerReachable step a b := by
  induction xs generalizing a with
  | nil =>
      change a = b at hchain
      subst b
      exact PachnerReachable.refl a
  | cons c cs ih =>
      change step a c ∧ IsPachnerChain step c cs b at hchain
      exact (reachable_of_step hchain.1).trans (ih hchain.2)

/-- Reachability is exactly existence of a finite certificate chain. -/
theorem reachable_iff_exists_finite_chain {K : Type u} {step : K → K → Prop}
    {a b : K} :
    PachnerReachable step a b ↔
      ∃ xs : List K, IsPachnerChain step a xs b := by
  constructor
  · exact reachable_has_finite_chain
  · rintro ⟨xs, hxs⟩
    exact finite_chain_reachable hxs

#print axioms MillenniumSuite.PNPPC.reachable_iff_exists_finite_chain

end MillenniumSuite.PNPPC
