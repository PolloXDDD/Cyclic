import Mathlib

/-!
# Extensional P and NP over a costed machine model

The model separates operational semantics from complexity definitions.  A
`MachineModel` supplies deterministic deciders, nondeterministic verifiers,
their cost functions, and the standard embedding of a decider into a verifier
that ignores the witness.
-/

universe u

namespace MillenniumSuite.RHPNP

abbrev BitString := List Bool
abbrev Language := Set BitString

/-- Polynomial bound in input length. -/
def PolyBound (f : BitString → ℕ) : Prop :=
  ∃ c k : ℕ, ∀ x : BitString, f x ≤ c * (x.length + 1) ^ k

/-- Operational interface used by the complexity classes. -/
structure MachineModel where
  Decider : Type u
  Verifier : Type u
  run : Decider → BitString → Bool
  deciderCost : Decider → BitString → ℕ
  verify : Verifier → BitString → BitString → Bool
  verifierCost : Verifier → BitString → BitString → ℕ
  lift : Decider → Verifier
  lift_run : ∀ d x w, verify (lift d) x w = run d x
  lift_cost : ∀ d x w, verifierCost (lift d) x w ≤ deciderCost d x

/-- Deterministic polynomial-time decidability. -/
def InP (M : MachineModel) (L : Language) : Prop :=
  ∃ d : M.Decider,
    (∀ x : BitString, M.run d x = true ↔ x ∈ L) ∧
    PolyBound (M.deciderCost d)

/-- Nondeterministic polynomial-time verifiability with polynomial witness length. -/
def InNP (M : MachineModel) (L : Language) : Prop :=
  ∃ v : M.Verifier,
    (∃ c q : ℕ, ∀ x : BitString,
      x ∈ L ↔ ∃ w : BitString,
        w.length ≤ c * (x.length + 1) ^ q ∧ M.verify v x w = true) ∧
    (∃ c k : ℕ, ∀ x w : BitString,
      M.verifierCost v x w ≤ c * (x.length + 1) ^ k)

/-- Extensional equality of the two complexity classes. -/
def PEqualsNP (M : MachineModel) : Prop :=
  ∀ L : Language, InP M L ↔ InNP M L

end MillenniumSuite.RHPNP
