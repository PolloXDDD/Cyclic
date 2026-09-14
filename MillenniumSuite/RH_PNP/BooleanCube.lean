import MillenniumSuite.RH_PNP.ProblemStatement
import Mathlib

/-!
# Boolean cube to symmetric cube

The manuscript uses the coordinate change `z_i = 1 - 2 x_i` from Boolean
assignments to the symmetric cube `{-1,1}^n`.  This module constructs that map
as an actual equivalence.
-/

set_option autoImplicit false

namespace MillenniumSuite.RHPNP

/-- Boolean value as an integer bit. -/
def boolBit : Bool → ℤ
  | false => 0
  | true => 1

/-- The manuscript's coordinate map `z = 1 - 2x`. -/
def boolToSign (b : Bool) : ℤ := 1 - 2 * boolBit b

@[simp] theorem boolToSign_false : boolToSign false = 1 := by
  rfl

@[simp] theorem boolToSign_true : boolToSign true = -1 := by
  rfl

/-- Every encoded Boolean coordinate lies in `{-1,1}`. -/
theorem boolToSign_mem (b : Bool) :
    boolToSign b = 1 ∨ boolToSign b = -1 := by
  cases b <;> simp

/-- The coordinate encoding is injective. -/
theorem boolToSign_injective : Function.Injective boolToSign := by
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Integer-valued realization of the symmetric Boolean cube. -/
def SymmetricCube (n : Nat) :=
  {z : Fin n → ℤ // ∀ i, z i = 1 ∨ z i = -1}

/-- Coordinatewise Boolean-to-sign encoding. -/
def assignmentToSymmetricCube {n : Nat} (a : Assignment n) : SymmetricCube n :=
  ⟨fun i => boolToSign (a i), fun i => boolToSign_mem (a i)⟩

/-- Decode `1` as `false` and `-1` as `true`. -/
def symmetricCubeToAssignment {n : Nat} (z : SymmetricCube n) : Assignment n :=
  fun i => if z.1 i = 1 then false else true

/-- Decoding after encoding returns the original Boolean assignment. -/
theorem symmetricCubeToAssignment_assignmentToSymmetricCube {n : Nat}
    (a : Assignment n) :
    symmetricCubeToAssignment (assignmentToSymmetricCube a) = a := by
  funext i
  cases h : a i <;> simp [symmetricCubeToAssignment, assignmentToSymmetricCube, h]

/-- Encoding after decoding returns the original point of the symmetric cube. -/
theorem assignmentToSymmetricCube_symmetricCubeToAssignment {n : Nat}
    (z : SymmetricCube n) :
    assignmentToSymmetricCube (symmetricCubeToAssignment z) = z := by
  apply Subtype.ext
  funext i
  rcases z.property i with hi | hi
  · simp [assignmentToSymmetricCube, symmetricCubeToAssignment, hi]
  · simp [assignmentToSymmetricCube, symmetricCubeToAssignment, hi]

/-- Exact finite equivalence between `{0,1}^n` and `{-1,1}^n`. -/
def assignmentSymmetricCubeEquiv (n : Nat) :
    Assignment n ≃ SymmetricCube n where
  toFun := assignmentToSymmetricCube
  invFun := symmetricCubeToAssignment
  left_inv := symmetricCubeToAssignment_assignmentToSymmetricCube
  right_inv := assignmentToSymmetricCube_symmetricCubeToAssignment

#print axioms MillenniumSuite.RHPNP.boolToSign_injective
#print axioms MillenniumSuite.RHPNP.symmetricCubeToAssignment_assignmentToSymmetricCube
#print axioms MillenniumSuite.RHPNP.assignmentToSymmetricCube_symmetricCubeToAssignment

end MillenniumSuite.RHPNP
