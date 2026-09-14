# PC -> NS source alignment

Source: `A Cyclic Equi-Transduction of the Millennium Suite`, first transduction.

| Manuscript step | Lean module | Current declaration/status |
|---|---|---|
| `M^3 ≅ S^3` under the smooth Poincare antecedent | `PC_NS/Geometry.lean` | `smooth_equiv_sphere_of_poincare` — implemented |
| Unit round sphere normalization | `PC_NS/Geometry.lean` | `sphere3_radius`, `sphere3_norm` — implemented |
| Enstrophy balance, manuscript Eq. 128 | `PC_NS/ProblemStatement.lean` | `EnstrophyBalance` — exact target predicate |
| Young/stretching estimate, manuscript Eq. 136 | `PC_NS/ProblemStatement.lean` | `StretchingBound` — exact target predicate |
| Balance + stretching => differential bound | `PC_NS/Enstrophy.lean` | `enstrophy_differential_bound` — implemented |
| Positive Ricci/viscous damping signs | `PC_NS/Enstrophy.lean` | `physical_damping_signs` — implemented |
| Cubic absorption below curvature scale | `PC_NS/Enstrophy.lean` | `cubic_absorbed_by_ricci`, refined differential bound — implemented |
| Uniform enstrophy estimate, manuscript Eq. 140 | `PC_NS/ProblemStatement.lean` | `UniformEnstrophyTarget` — open construction target |
| BKM finite integral | `PC_NS/BKM.lean` | `BKMFinite`; continuous-profile lemma implemented |
| PDE-specific BKM continuation | planned `PC_NS/Continuation.lean` | next proof layer |
| Full global smooth Navier--Stokes theorem | planned `PC_NS/Theorem.lean` | exported only after all previous layers close |

The project intentionally does **not** create `PCNSCertificate`, an axiom for
`PC -> NS`, or a theorem whose arguments already contain the missing analytic
conclusions.
