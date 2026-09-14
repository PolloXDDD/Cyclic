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

/-- The pointwise scattering quotient is exactly the quotient of its numerator
and denominator functions. -/
theorem scattering_eq_fun_div (xi : CompletedZeta) :
    scattering xi = scatteringNumerator xi / scatteringDenominatorFun xi := by
  funext s
  rfl

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
  rw [scattering_eq_fun_div xi]
  exact meromorphicOrderAt_div hnum hden

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

/-- Mathlib's actual completed Riemann zeta is meromorphic at every complex
point.  We obtain this from its decomposition into the entire corrected
completed zeta plus the two rational polar terms. -/
theorem actual_completed_zeta_meromorphicAt (s : ℂ) :
    MeromorphicAt completedRiemannZeta s := by
  have h0 : MeromorphicAt completedRiemannZeta₀ s :=
    (differentiable_completedZeta₀.analyticAt s).meromorphicAt
  have hdivId : MeromorphicAt (fun z : ℂ => 1 / z) s := by
    fun_prop
  have hdivOneSub : MeromorphicAt (fun z : ℂ => 1 / (1 - z)) s := by
    fun_prop
  have hrhs : MeromorphicAt
      ((completedRiemannZeta₀ - (fun z : ℂ => 1 / z)) - (fun z : ℂ => 1 / (1 - z))) s :=
    (h0.sub hdivId).sub hdivOneSub
  refine hrhs.congr ?_
  filter_upwards with z
  simpa only [Pi.sub_apply] using (completedRiemannZeta_eq z).symm

/-- Consequently the actual scattering numerator is meromorphic everywhere. -/
theorem actual_scattering_numerator_meromorphicAt (s : ℂ) :
    MeromorphicAt (scatteringNumerator completedRiemannZeta) s := by
  have hbase := actual_completed_zeta_meromorphicAt (2 * s - 1)
  have haff : AnalyticAt ℂ (fun z : ℂ => 2 * z - 1) s := by
    fun_prop
  have hcomp : MeromorphicAt
      (completedRiemannZeta ∘ (fun z : ℂ => 2 * z - 1)) s :=
    hbase.comp_analyticAt (g := fun z : ℂ => 2 * z - 1) haff
  simpa [scatteringNumerator, Function.comp_def] using hcomp

/-- Consequently the actual scattering denominator is meromorphic everywhere. -/
theorem actual_scattering_denominator_meromorphicAt (s : ℂ) :
    MeromorphicAt (scatteringDenominatorFun completedRiemannZeta) s := by
  have hbase := actual_completed_zeta_meromorphicAt (2 * s)
  have haff : AnalyticAt ℂ (fun z : ℂ => 2 * z) s := by
    fun_prop
  have hcomp : MeromorphicAt
      (completedRiemannZeta ∘ (fun z : ℂ => 2 * z)) s :=
    hbase.comp_analyticAt (g := fun z : ℂ => 2 * z) haff
  simpa [scatteringDenominatorFun, Function.comp_def] using hcomp

/-- Exact local order data still needed at a candidate zero `rho` to obtain a
simple scattering pole at `rho/2`.  This is deliberately a definition, not an
asserted theorem. -/
def SimpleScatteringOrderData (rho : ℂ) : Prop :=
  MeromorphicAt (scatteringNumerator completedRiemannZeta) (rho / 2) ∧
  MeromorphicAt (scatteringDenominatorFun completedRiemannZeta) (rho / 2) ∧
  meromorphicOrderAt (scatteringNumerator completedRiemannZeta) (rho / 2) = 0 ∧
  meromorphicOrderAt (scatteringDenominatorFun completedRiemannZeta) (rho / 2) = 1

/-- Since meromorphicity is now proved unconditionally, the remaining local
input can be reduced to the two multiplicity statements alone. -/
def SimpleScatteringMultiplicityData (rho : ℂ) : Prop :=
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

/-- After proving global meromorphicity, multiplicity data alone produce the
simple scattering pole. -/
theorem actual_scattering_simple_pole_of_multiplicity_data
    (rho : ℂ) (h : SimpleScatteringMultiplicityData rho) :
    meromorphicOrderAt (scattering completedRiemannZeta) (rho / 2) =
      ((-1 : ℤ) : WithTop ℤ) := by
  rcases h with ⟨hnumOrder, hdenOrder⟩
  exact scattering_order_eq_neg_one_of_orders completedRiemannZeta (rho / 2)
    (actual_scattering_numerator_meromorphicAt (rho / 2))
    (actual_scattering_denominator_meromorphicAt (rho / 2))
    hnumOrder hdenOrder

#print axioms MillenniumSuite.BSDRH.scattering_eq_fun_div
#print axioms MillenniumSuite.BSDRH.scattering_order_eq_sub
#print axioms MillenniumSuite.BSDRH.scattering_order_eq_neg_one_of_orders
#print axioms MillenniumSuite.BSDRH.actual_completed_zeta_meromorphicAt
#print axioms MillenniumSuite.BSDRH.actual_scattering_numerator_meromorphicAt
#print axioms MillenniumSuite.BSDRH.actual_scattering_denominator_meromorphicAt
#print axioms MillenniumSuite.BSDRH.actual_scattering_simple_pole_of_order_data
#print axioms MillenniumSuite.BSDRH.actual_scattering_simple_pole_of_multiplicity_data

end MillenniumSuite.BSDRH
