## What changed

Proved all three theorems in `Sheaf.SecSmoothPurity.TransportFiniteEncoding`.
`finiteConstants_spec` reuses the existing local bijectivity instances for the
specified constant-function map, applies sheafification, and composes with its
counit isomorphism. Added a private `import all` of
`Sheaf.Paper.FiniteDiscreteCondensedRing` to access those proved instances.
`finiteModuleEncoding_isEquivalence` uses the existing equivalence instance for
the concrete scalar-action functor. `finiteModuleEncoding_forget` is reflexivity.
Updated the node proof and dependencies to record these existing arguments.
All declaration signatures, definitions and public imports are unchanged.

## Proved and sorry left

Closed 3 of 3 original holes (namespace
`AlgebraicGeometry.ProEtale.PurityTransport`):

- `finiteConstants_spec`
- `finiteModuleEncoding_isEquivalence`
- `finiteModuleEncoding_forget`

No sorry remains in the item. No holes added; no statements split off.

## No longer needed

None. The original node had no proof dependencies to prune. No existing imports,
nodes, modules or unit steps are removed. The proof reuses the two existing
concrete constructions rather than rebuilding local gluing or tensor actions.

## Where the brief, the DAG or earlier work was wrong

The node had an empty proof plan despite its three theorem holes. Its proof now
records the existing concrete proofs that discharge them. No mathematical
statement or definition needed repair.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
