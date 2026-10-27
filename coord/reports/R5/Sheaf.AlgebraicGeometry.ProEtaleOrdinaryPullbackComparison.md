## What changed

Proved `AlgebraicGeometry.Scheme.AcyclicHypercover.existsUnique_composition` by applying
`AlgebraicGeometry.Scheme.exchangeModuleComposition_existsUnique` to `k`, `h`, `R`, `S`,
`T`, `c`, `d`. Its normalization predicate unfolds to exactly the existing section equation.
Added the proof-only import `Sheaf.Paper.StrictTowerOperations`; kept the public import,
all declaration signatures, docstrings and the `compositionIso` construction unchanged.
Updated the owning node's proof, proof dependencies and proof origin to record this reuse.

The reused theorem is a tool from `def-weil-pbc-strict-tower-operations` (proper-base-change
unit). It already proves the exact arbitrary-ring-sheaf ordinary comparison; this item's
unit has no separate theorem supplying it. No unit statement or realized step is bypassed.
Both the Lean import check and a DAG dependency traversal show that reuse creates no cycle.
No maintainer tool-use approval was changed or added.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.AcyclicHypercover.existsUnique_composition`
(node `def-sfb-proetale-ordinary-pullback-comparison`).
Added 0 holes; 0 holes remain in the delivered module. No split-off statements.
The reused theorem is already proved; its existing proof ultimately uses
`proEtaleRingDerivedPullbackComposition`, whose existing sorry remains outside this packet.
This delivery does not claim to close that dependency.

## No longer needed

None: no imports, nodes or modules removed. The original node had no proof dependencies.
The shorter proof reuses the already-proved ordinary comparison, so no new sectionwise
construction, adjunction-normalization proof, or derived/K-flat intermediate result is added.

## Where the brief, the DAG or earlier work was wrong

The item was already stated and proved, with its section equation packaged as
`ExchangeModuleCompositionNormalized`, in `Sheaf.Paper.StrictTowerOperations`.
The original owning node recorded no proof route. Its new route records this exact reuse.
The coefficient identifications, universes and normalization agree definitionally, including
identity morphisms, zero ring sheaves and empty schemes; there are no additional hypotheses.
No statement or definition repair was needed.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
