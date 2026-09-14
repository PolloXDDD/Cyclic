import Mathlib

universe u

namespace MillenniumSuite.NSYM

/-- Semantic data needed to state the four-dimensional pure Yang--Mills target. -/
structure YangMillsModel where
  Theory : Type u
  IsFourDimensionalPure : Theory → Prop
  ExistsAxiomaticQuantumTheory : Theory → Prop
  MassGap : Theory → ℝ

/-- Existence plus a strictly positive spectral gap for every theory in scope. -/
def YangMillsExistenceAndMassGap (M : YangMillsModel) : Prop :=
  ∀ T : M.Theory,
    M.IsFourDimensionalPure T →
      M.ExistsAxiomaticQuantumTheory T ∧ 0 < M.MassGap T

/-- Exact implication shape of Transduction II. -/
def NSYMBridgeTarget (NavierStokesGlobalRegularity : Prop)
    (M : YangMillsModel) : Prop :=
  NavierStokesGlobalRegularity → YangMillsExistenceAndMassGap M

end MillenniumSuite.NSYM
