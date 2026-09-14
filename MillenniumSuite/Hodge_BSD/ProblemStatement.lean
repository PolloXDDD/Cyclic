import Mathlib

/-!
# Hodge -> BSD: rank-comparison layer

The manuscript reaches BSD by deriving the two opposite inequalities between
Mordell--Weil rank and analytic order of vanishing.  We formalize that exact
logical endpoint separately from the still-to-be-built regulator and Euler
system machinery.
-/

namespace MillenniumSuite.HodgeBSD

/-- The two integer invariants appearing in the BSD rank equality. -/
structure RankData where
  mordellWeilRank : ℕ
  analyticOrder : ℕ

/-- Algebraic-cycle/regulator side of the manuscript. -/
def AlgebraicLowerBound (d : RankData) : Prop :=
  d.mordellWeilRank ≤ d.analyticOrder

/-- Selmer/Euler-system side of the manuscript. -/
def SelmerUpperBound (d : RankData) : Prop :=
  d.analyticOrder ≤ d.mordellWeilRank

/-- BSD rank equality for this datum. -/
def BSDRankEquality (d : RankData) : Prop :=
  d.mordellWeilRank = d.analyticOrder

/-- Final rank-comparison subtarget extracted from Transduction IV. -/
def OppositeBoundsGiveBSD : Prop :=
  ∀ d : RankData,
    AlgebraicLowerBound d → SelmerUpperBound d → BSDRankEquality d

end MillenniumSuite.HodgeBSD
