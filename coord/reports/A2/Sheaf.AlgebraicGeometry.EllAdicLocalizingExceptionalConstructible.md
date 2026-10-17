## What changed

Closed `ellAdic_localizing_rightAdjoint_obj_boundedConstructible` by combining the finite
cohomological amplitude and degreewise constructibility components through
`mem_boundedConstructible_iff`.  The two geometric components are stated as separate
intermediate theorems in new modules, with their source and proof obligations documented.

## Proved and sorry left

Proved:

- `AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_boundedConstructible`.

Sorry left (new strictly smaller components):

- `ellAdic_localizing_rightAdjoint_obj_isBounded`.
- `ellAdic_localizing_rightAdjoint_obj_homology_constructible`.

The delivery closes 1 target hole and adds 2 component holes.

## No longer needed

The target module no longer directly imports these proof-only modules; they are imported by
the component modules instead:

- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`.
- `Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient`.
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`.
- `Sheaf.Paper.IntegralLfpLocalTorsionCharts`.
- `Sheaf.Paper.IntegralLfpLocallyFreeResolution`.

The abandoned trial module `lean/Sheaf/AlgebraicGeometry/EllAdicLocalizingExceptionalConstructibleIso.lean`
was withdrawn; it was replaced by the two component statements above.

## Where the brief, the DAG or earlier work was wrong

The original single proof obligation combines two independent geometric facts: finite
cohomological amplitude and constructibility of every cohomology object.  No existing
declaration in the repository states either fact for the supplied arbitrary localizing
right adjoint.  Treating the whole conclusion as one representative-isomorphism theorem
would merely rename the target, so that route was discarded.  The target DAG copy now
records the two component nodes and the real predicate-combination proof.

## New nodes

- `lem-sfb-adic-localizing-exceptional-bounded`:
  `ellAdic_localizing_rightAdjoint_obj_isBounded`.
- `lem-sfb-adic-localizing-exceptional-cohomology`:
  `ellAdic_localizing_rightAdjoint_obj_homology_constructible`.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
