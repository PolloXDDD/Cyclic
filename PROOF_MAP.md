# Proof map — OpenAI-style formalization

The old `CycleCertificates` architecture is retired. A bridge may use exactly
its mathematical antecedent (for example the `PC` hypothesis when proving
`PC -> NS`), but it may not receive a record containing the missing bridge
lemmas.

Each bridge follows:

1. `ProblemStatement.lean` — exact propositions/data interfaces only.
2. `Construction.lean` / geometry/analytic modules — explicit mathematical objects.
3. Small theorem modules — identities, regularity, bounds, invariants.
4. `Theorem.lean` — final implication assembled only from proved modules.
5. `Audit.lean` — `#print axioms` on exported results.

## PC -> NS — active

Implemented now:

- exact unit 3-sphere model;
- smooth Poincare antecedent;
- elimination to a smooth equivalence with the sphere;
- exact scalar enstrophy balance predicate from the paper;
- exact vortex-stretching bound predicate from the paper;
- proved balance+stretching differential inequality;
- proved signs of viscous and Ricci damping terms;
- BKM finite-integral predicate and compact-interval integrability for continuous profiles.

Next construction layer:

- define the actual vorticity and covariant derivative objects on the round sphere;
- prove the Bochner--Weitzenbock identity used by the manuscript;
- construct the enstrophy trajectory from a Navier--Stokes solution;
- prove the uniform bound `UniformEnstrophyTarget`;
- formalize the PDE-specific BKM continuation step;
- only then export `PC_NS/Theorem.lean`.

## RH -> P=NP — active

Already implemented:

- finite Boolean syntax;
- explicit recursive literal/clause/formula penalty;
- proof that formula penalty zero iff the CNF is satisfied;
- existential zero-penalty encoding theorem.

Next layers are zeta-zero data, GUE statement, Weyl sequence, discrepancy, QMC,
prime duality, algorithm, and complexity accounting.

## Remaining bridges

- `NS_YM/`: connection construction, curvature/action bounds, correlation/mass gap.
- `YM_Hodge/`: bundle/connection construction, Dolbeault integrability,
  Hermitian--Einstein stage, cycle-class endpoint.
- `Hodge_BSD/`: self-product, cycles, regulator/height, analytic-rank endpoint.
- `BSD_RH/`: twist family, automorphic scattering, Maass--Selberg, zero location.
- `PNP_PC/`: triangulations, sphere-recognition language, verification, topology.

## Proof gate

No final bridge is exported as proved until:

- no `sorry`, `admit`, project `axiom`, or project `constant` is in its dependency tree;
- existential objects have explicit Lean witnesses;
- quantitative inequalities are proved in separate lemmas;
- `#print axioms` reports only accepted kernel principles;
- `lake build` succeeds with warnings as errors.
