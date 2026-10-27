## What changed

Four refinement consequences are proved in the assigned module. Source and target
refinement normalization follow by transporting `refinement_normalization` through
the existing kappa corners. Invertibility follows from the constant-tower refinement
comparison. Common-refinement independence and cocycle follow from the existing
`commonRefinement_normalization` statement and `refinementExchangeCoherence`, by
cancelling the endpoint supportScalar isomorphisms.

All added helpers are private and proved. Public signatures, definitions, imports,
and previously proved declarations are preserved. A local section respects declaration
transparency while elaborating common-refinement comparisons. The final module
compiled cleanly through `lcompile.py` in 35.8 seconds.

## Proved and sorry left

Four of the twelve original holes are filled; zero holes are added or split off.
All declarations listed here are in
`AlgebraicGeometry.Scheme.StrictSupportNormalization` and belong to the existing
node `lem-pur-strict-reduction-compact-support-normalization`.

Filled:

- `targetRefinement_normalization`
- `sourceRefinement_normalization`
- `refinement_isIso`
- `commonRefinement_coherence`

The eight original holes retained, with their existing source and proof docstrings,
are:

- `strictReductionCompactSupportNormalization`
- `scalarPull_composition`
- `inputPull_composition`
- `refinement_normalization`
- `refinement_exchange`
- `inputPull_identity`
- `commonRefinement_normalization`
- `scalarPush_composition`

The proofs use the existing named refinement and common-refinement normalization
obligations; those obligations are not claimed as proved. No new statement moves an
existing hole.

## No longer needed

None. No import, dependency, node, or module is withdrawn. The existing planned
refinement and common-refinement route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found in the four clauses proved here. Optional
quasi-compactness proof arguments in the constant-tower comparison APIs require
explicit proof-irrelevance rewrites to avoid costly unfolding during conversion.
The delivered proofs use those rewrites without changing any definition.

The proper/open assembly for the main normalization and the common-refinement
normalization were also investigated. Their current proof drafts encounter expensive
conversion checks and are not included in this delivery. The original obligations
and their planned dependencies remain intact.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
