import Mathlib

/-!
# Gauge connection and curvature on Euclidean four-space

This is the differential-geometric algebraic skeleton of the connection used in
Transduction II.  The coefficient algebra is any real normed algebra; matrix Lie
algebras are instances of this setup.
-/

noncomputable section

namespace MillenniumSuite.NSYM

abbrev Space4 := EuclideanSpace ℝ (Fin 4)

/-- A gauge connection in a fixed trivialization. -/
abbrev Connection (A : Type*) := Fin 4 → Space4 → A

/-- Standard Euclidean coordinate vector. -/
def coordinateVector4 (mu : Fin 4) : Space4 :=
  EuclideanSpace.single mu 1

/-- Directional derivative of an algebra-valued field in the `mu` coordinate. -/
def directionalDerivative {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : Space4 → A) (mu : Fin 4) (x : Space4) : A :=
  fderiv ℝ f x (coordinateVector4 mu)

/-- Lie-algebra commutator in an associative coefficient algebra. -/
def commutator {A : Type*} [Ring A] (X Y : A) : A :=
  X * Y - Y * X

/-- Curvature tensor `F_{mu nu} = d_mu A_nu - d_nu A_mu + [A_mu,A_nu]`. -/
def curvature {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A]
    (conn : Connection A) (mu nu : Fin 4) (x : Space4) : A :=
  directionalDerivative (conn nu) mu x -
    directionalDerivative (conn mu) nu x +
    commutator (conn mu x) (conn nu x)

/-- The commutator is antisymmetric. -/
theorem commutator_swap {A : Type*} [Ring A] (X Y : A) :
    commutator X Y = -commutator Y X := by
  unfold commutator
  abel

/-- Gauge curvature is antisymmetric in its coordinate indices. -/
theorem curvature_swap {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A]
    (conn : Connection A) (mu nu : Fin 4) (x : Space4) :
    curvature conn mu nu x = -curvature conn nu mu x := by
  unfold curvature
  rw [commutator_swap]
  abel

/-- Diagonal curvature components vanish. -/
@[simp] theorem curvature_self {A : Type*}
    [NormedRing A] [NormedAlgebra ℝ A]
    (conn : Connection A) (mu : Fin 4) (x : Space4) :
    curvature conn mu mu x = 0 := by
  simp [curvature, commutator]

#print axioms MillenniumSuite.NSYM.curvature_swap
#print axioms MillenniumSuite.NSYM.curvature_self

end MillenniumSuite.NSYM
