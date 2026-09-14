# Proof map — OpenAI-style formalization

The old `CycleCertificates` architecture is retired. A bridge may use exactly
its mathematical antecedent, but it may not receive a record containing the
missing bridge lemmas.

Each bridge follows:

1. `ProblemStatement.lean` — exact propositions/data interfaces only.
2. construction/geometry/analytic modules — explicit mathematical objects.
3. small theorem modules — identities, regularity, bounds, invariants.
4. `Theorem.lean` — final implication assembled only from proved modules.
5. `Audit.lean` — `#print axioms` on exported results.

## PC -> NS — active

Implemented: exact unit 3-sphere; smooth Poincare antecedent; smooth equivalence
elimination; scalar enstrophy balance; vortex-stretching bound; derived
differential inequality; viscous/Ricci damping signs; curvature-threshold
absorption; BKM finite-integral layer.

Next: actual vorticity/covariant derivatives, Bochner--Weitzenbock, construction
of the enstrophy trajectory, global bound, and PDE continuation.

## NS -> YM — active

Implemented: quantified Yang--Mills existence/mass-gap statement; correlation
length data; manuscript hypotheses `xi > 0`, `eta > 0`, `delta = xi^-1`; proved
strict positivity of the resulting mass gap and positivity of `eta^-1`.

Next: temporal connection from velocity, curvature identity/bound, Euclidean
action estimate, Uhlenbeck extension, and the analytic derivation of correlation
decay from the Navier--Stokes side.

## YM -> Hodge — active

Implemented: exact scalar Yang--Mills energy decomposition used by the paper;
proved that absolute topological minimality forces both Hermitian--Einstein
residuals to vanish; quantified Hodge-conjecture semantic statement.

Next: bundle/Chern-character construction, Dolbeault integrability,
Koszul--Malgrange/Donaldson--Uhlenbeck--Yau interfaces, Chow/cycle-class endpoint.

## Hodge -> BSD — active

Implemented: rank-comparison data; proved that the two manuscript inequalities
give BSD rank equality by antisymmetry; added a Mathlib-level weak BSD statement
over actual rational Weierstrass curves, meromorphic L-functions,
`meromorphicOrderAt`, and Mordell--Weil free rank.

Next: self-products, algebraic cycles, height pairing/regulator, Beilinson--Bloch
lower bound, Selmer/Euler-system upper bound.

## BSD -> RH — active

Implemented: completed-zeta/scattering objects; functional equation; proved zero
symmetry `rho -> 1-rho`; proved that a zero `rho` makes the scattering
denominator vanish at `rho/2`; exact Mathlib `RiemannHypothesis` target.

Next: modular/twist family, scattering analyticity/unitarity, Maass--Selberg
identity, residue sign contradiction, off-critical-line exclusion.

## RH -> P=NP — active

Implemented: Boolean CNF syntax; explicit literal/clause/formula penalty; proof
that penalty zero iff satisfied; existential zero-penalty theorem; costed machine
model; formal `InP`, `InNP`, and `PEqualsNP`; proof `P ⊆ NP`; proof that `P=NP`
is equivalent to the reverse inclusion in this model.

Next: zeta-zero data, GUE, Weyl vectors, discrepancy, QMC error, prime duality,
polynomial-time 3-SAT algorithm and transfer to all NP languages.

## P=NP -> PC — active

Implemented: inductive Pachner reachability; sphere-certificate predicate;
one-step reachability and concatenation of Pachner sequences.

Next: finite triangulation encoding, polynomial verifier, sphere-recognition
language, `P=NP` complexity transfer, Ricci-surgery/topological endpoint.

## Proof gate

No final bridge is exported as proved until no `sorry`, `admit`, project `axiom`,
or project `constant` occurs in its dependency tree; existential objects have
explicit witnesses; inequalities are proved separately; `#print axioms` is
clean; and `lake build` succeeds with warnings as errors.
