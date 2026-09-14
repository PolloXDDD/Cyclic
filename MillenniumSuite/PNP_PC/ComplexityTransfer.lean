import MillenniumSuite.PNP_PC.Pachner
import MillenniumSuite.RH_PNP.ComplexityBasic

namespace MillenniumSuite.PNPPC

open MillenniumSuite.RHPNP

/-- The complexity-theoretic step used in the manuscript: if `P = NP`, then any
sphere-recognition language already known to lie in NP lies in P. -/
theorem sphere_recognition_inP_of_pEqualsNP
    (M : MachineModel) (sphereLanguage : Language)
    (hEq : PEqualsNP M) (hNP : InNP M sphereLanguage) :
    InP M sphereLanguage := by
  exact inP_of_pEqualsNP M sphereLanguage hEq hNP

#print axioms MillenniumSuite.PNPPC.sphere_recognition_inP_of_pEqualsNP

end MillenniumSuite.PNPPC
