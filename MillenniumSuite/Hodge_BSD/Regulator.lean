import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Neron--Tate regulator positivity layer

The manuscript uses positivity of the Neron--Tate height pairing matrix to
conclude that the regulator determinant is strictly positive.  This module
formalizes that linear-algebra implication using Mathlib's genuine
positive-definite matrix predicate.
-/

namespace MillenniumSuite.HodgeBSD

open Matrix

/-- A positive-definite real height matrix has strictly positive determinant. -/
theorem posDef_regulator_det_pos {n : Type*}
    [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.PosDef) :
    0 < H.det := by
  exact hH.det_pos

/-- Strict positivity immediately gives non-vanishing of the regulator. -/
theorem posDef_regulator_det_ne_zero {n : Type*}
    [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.PosDef) :
    H.det ≠ 0 := by
  exact (posDef_regulator_det_pos H hH).ne'

/-- Consequently the regulator represented by this determinant cannot vanish. -/
theorem posDef_regulator_nonzero {n : Type*}
    [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.PosDef) :
    ¬ H.det = 0 :=
  posDef_regulator_det_ne_zero H hH

#print axioms MillenniumSuite.HodgeBSD.posDef_regulator_det_pos
#print axioms MillenniumSuite.HodgeBSD.posDef_regulator_det_ne_zero

end MillenniumSuite.HodgeBSD
