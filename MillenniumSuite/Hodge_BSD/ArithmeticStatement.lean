import Mathlib

/-!
# Arithmetic BSD statement over Q

This file states the weak rank form used by the manuscript with Mathlib's actual
Weierstrass curves, meromorphic functions, L-series, meromorphic order, and free
rank.  It is a definition only: no open arithmetic theorem is postulated.
-/

noncomputable section

namespace MillenniumSuite.HodgeBSD

open scoped Topology

/-- A meromorphic continuation agreeing with the elliptic-curve L-series in its
classical right half-plane. -/
def IsEllipticLFunction (E : WeierstrassCurve ℚ) (L : ℂ → ℂ) : Prop :=
  Meromorphic L ∧ ∀ s : ℂ, 3 / 2 < s.re → L s = E.LSeries s

/-- Weak BSD over `ℚ`: analytic order at one equals Mordell--Weil free rank. -/
def WeakBSDQ : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] [AddGroup.FG E.toAffine.Point]
    (L : ℂ → ℂ),
    IsEllipticLFunction E L →
      meromorphicOrderAt L 1 = AddCommGroup.freeRank E.toAffine.Point

end MillenniumSuite.HodgeBSD
