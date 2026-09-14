import Mathlib.Analysis.Matrix.Order

/-!
# Neron--Tate regulator nondegeneracy layer

The manuscript uses positivity of the Neron--Tate height pairing to conclude that
the regulator determinant is nonzero.  This module isolates that exact linear-
algebra implication using Mathlib's genuine positive-definite matrix predicate.
-/

namespace MillenniumSuite.HodgeBSD

open Matrix

/-- A positive-definite real height matrix has nonzero determinant. -/
theorem posDef_regulator_det_ne_zero {n : Type*}
    [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.PosDef) :
    H.det ≠ 0 := by
  have hPSD : H.PosSemidef := hH.posSemidef
  exact (hPSD.posDef_iff_det_ne_zero).mp hH

/-- Consequently the regulator represented by this determinant cannot vanish. -/
theorem posDef_regulator_nonzero {n : Type*}
    [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.PosDef) :
    ¬ H.det = 0 :=
  posDef_regulator_det_ne_zero H hH

#print axioms MillenniumSuite.HodgeBSD.posDef_regulator_det_ne_zero

end MillenniumSuite.HodgeBSD
