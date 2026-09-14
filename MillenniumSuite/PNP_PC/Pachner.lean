import MillenniumSuite.PNP_PC.ProblemStatement

universe u

namespace MillenniumSuite.PNPPC

/-- One elementary move yields a reachable state. -/
theorem reachable_of_step {K : Type u} {step : K → K → Prop}
    {a b : K} (h : step a b) : PachnerReachable step a b := by
  exact PachnerReachable.move (PachnerReachable.refl a) h

/-- Pachner reachability is transitive, so two valid move sequences concatenate. -/
theorem PachnerReachable.trans {K : Type u} {step : K → K → Prop}
    {a b c : K} (hab : PachnerReachable step a b)
    (hbc : PachnerReachable step b c) : PachnerReachable step a c := by
  induction hbc with
  | refl => exact hab
  | move hreach hstep ih =>
      exact PachnerReachable.move ih hstep

/-- A certificate can be extended by one additional elementary move. -/
theorem extend_sphere_certificate {K : Type u} {step : K → K → Prop}
    {standard input next : K}
    (hcert : HasSphereCertificate step standard input)
    (hstep : step standard next) :
    PachnerReachable step input next := by
  exact PachnerReachable.move hcert hstep

#print axioms MillenniumSuite.PNPPC.PachnerReachable.trans

end MillenniumSuite.PNPPC
