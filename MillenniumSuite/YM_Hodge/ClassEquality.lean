import MillenniumSuite.YM_Hodge.HodgeStatement

namespace MillenniumSuite.YMHodge

theorem algebraic_class_of_eq
    (M : HodgeModel) (X : M.Variety) (p : ℕ)
    (a b : M.CohomologyClass X p)
    (hab : a = b)
    (hb : M.AlgebraicCycleClass X p b) :
    M.AlgebraicCycleClass X p a := by
  simpa [hab] using hb

#print axioms MillenniumSuite.YMHodge.algebraic_class_of_eq

end MillenniumSuite.YMHodge
