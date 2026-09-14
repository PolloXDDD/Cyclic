import MillenniumSuite.Hodge_BSD.ProblemStatement

namespace MillenniumSuite.HodgeBSD

theorem bounds_give_rank_equality : OppositeBoundsGiveBSD := by
  intro d h1 h2
  exact Nat.le_antisymm h1 h2

#print axioms MillenniumSuite.HodgeBSD.bounds_give_rank_equality

end MillenniumSuite.HodgeBSD
