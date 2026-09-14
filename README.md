# MillenniumSuite — Lean 4 formalization

This project formalizes the cyclic Millennium-suite manuscript using the proof
engineering pattern of `openai/NavierStokesAndEuler`:

`ProblemStatement -> explicit objects -> local lemmas -> final theorem -> #print axioms`.

No bridge is represented by a proof-carrying certificate. Open mathematical
steps remain target propositions until the corresponding construction modules
prove them.

## Current work

### `PC_NS/`

The first transduction is now active. The project contains the exact unit
3-sphere model, a smooth Poincare antecedent, the manuscript's scalar enstrophy
balance and stretching predicates, and closed Lean proofs of the resulting
pointwise differential inequality and damping signs. The next modules will
construct those scalar quantities from an actual Navier--Stokes solution and
then formalize the uniform enstrophy/BKM continuation layer.

See `PC_NS_ALIGNMENT.md` for line-by-line source alignment.

### `RH_PNP/`

The finite SAT zero-penalty subconstruction is already explicit and proved.

## Toolchain

The project follows the OpenAI repository's toolchain:

- Lean 4.34.0-rc2
- Mathlib v4.34.0-rc2

## Build and audit

```bash
lake exe cache get
lake build
./scripts/audit.sh
```

The audit rejects project-level `sorry`, `admit`, `axiom`, and top-level
`constant` escape hatches and then builds the full project.
