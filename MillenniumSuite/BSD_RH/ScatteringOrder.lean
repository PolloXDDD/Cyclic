import MillenniumSuite.BSD_RH.ActualZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Tactic

/-!
# Meromorphic order of the scattering quotient

This module replaces the informal step "denominator zero gives a scattering
pole" by an exact meromorphic-order calculation.  The genuinely analytic
obligations are isolated as local facts about the orders of the numerator and
denominator; once those are known, Mathlib's quotient-order theorem closes the
pole calculation.
-/

noncomputable section

namespace MillenniumSuite.BSDRH

/-- Numerator of the manuscript's scalar scattering quotient
`Phi(s) = xi(2s-1) / xi(2s)`. -/
def scatteringNumerator (xi : CompletedZeta) : ℂ → ℂ :=
  fun s => xi (2 * s - 1)

/-- Denominator of the manuscript's scalar scattering quotient, as a function. -/
def scatteringDenominatorFun (xi : CompletedZeta) : ℂ → ℂ :=
  fun s => xi (2 * s)

@[simp] theorem scatteringNumerator_apply (xi : CompletedZeta) (s : ℂ) :
    scatteringNumerator xi s = xi (2 * s - 1) := rfl

@[simp] theorem scatteringDenominatorFun_apply (xi : CompletedZeta) (s : ℂ) :
    scatteringDenominatorFun xi s = scatteringDenominator xi s := rfl

/-- The meromorphic order of the scattering quotient is the numerator order
minus the denominator order.  This is a direct specialization of Mathlib's
`meromorphicOrderAt_div`. -/
theorem scattering_order_eq_sub
    (xi : CompletedZeta) (s : ℂ)
    (hnum : MeromorphicAt (scatteringNumerator xi) s)
    (hden : MeromorphicAt (scatteringDenominatorFun xi) s) :
    meromorphicOrderAt (scattering xi) s =
      meromorphicOrderAt (scatteringNumerator xi) s -
        meromorphicOrderAt (scatteringDenominatorFun xi) s := by
  simpa [scattering, scatteringNumerator, scatteringDenominatorFun] using
    (meromorphicOrderAt_div hnum hden)

/-- A regular nonvanishing numerator (order zero) divided by a simple zero of
the denominator (order one) has order `-1`.  In meromorphic language this is a
simple pole. -/
theorem scattering_order_eq_neg_one_of_orders
    (xi : CompletedZeta) (s : ℂ)
    (hnum : MeromorphicAt (scatteringNumerator xi) s)
    (hden : MeromorphicAt (scatteringDenominatorFun xi) s)
    (hnumOrder : meromorphicOrderAt (scatteringNumerator xi) s = 0)
    (hdenOrder : meromorphicOrderAt (scatteringDenominatorFun xi) s = 1) :
    meromorphicOrderAt (scattering xi) s = ((-1 : ℤ) : WithTop ℤ) := by
  rw [scattering_order_eq_sub xi s hnum hden, hnumOrder, hdenOrder]
  norm_num

/-- Exact local order data still needed at a candidate zero `rho` to obtain a
simple scattering pole at `rho/2`.  This is deliberately a definition, not an
asserted theorem. -/
def SimpleScatteringOrderData (rho : ℂ) : Prop :=
  MeromorphicAt (scatteringNumerator completedRiemannZeta) (rho / 2) ∧
  MeromorphicAt (scatteringDenominatorFun completedRiemannZeta) (rho / 2) ∧
  meromorphicOrderAt (scatteringNumerator completedRiemannZeta) (rho / 2) = 0 ∧
  meromorphicOrderAt (scatteringDenominatorFun completedRiemannZeta) (rho / 2) = 1

/-- The isolated order data imply an actual simple pole of the manuscript's
scattering quotient. -/
theorem actual_scattering_simple_pole_of_order_data
    (rho : ℂ) (h : SimpleScatteringOrderData rho) :
    meromorphicOrderAt (scattering completedRiemannZeta) (rho / 2) =
      ((-1 : ℤ) : WithTop ℤ) := by
  rcases h with ⟨hnum, hden, hnumOrder, hdenOrder⟩
  exact scattering_order_eq_neg_one_of_orders completedRiemannZeta (rho / 2)
    hnum hden hnumOrder hdenOrder

#print axioms MillenniumSuite.BSDRH.scattering_order_eq_sub
#print axioms MillenniumSuite.BSDRH.scattering_order_eq_neg_one_of_orders
#print axioms MillenniumSuite.BSDRH.actual_scattering_simple_pole_of_order_data

end MillenniumSuite.BSDRH
