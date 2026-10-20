## What changed

Proved `properOpenTowerComparison` by constructing the restriction-map isomorphism and
combining its structural normalization, open-adjunction unit identity, and finite-origin
evaluation normalization. The finite normalization theorem and the unit identity are
proved by explicit category-theoretic rewriting. The remaining structural comparisons are
isolated in one strictly smaller named theorem.

## Proved and sorry left

Closed:

- `properOpenTowerComparison`.
- `properOpenFiniteNormalization`.
- The unit identity conjunct of `properOpenNormalization`.

Left as one named component sorry:

- `properOpenComparisonNormalization` (invertibility, cartesian normalization, and
  adjunct equality of the explicit restriction map), node
  `lem-sp-proper-open-comparison-normalization`.

## No longer needed

Removed the provisional split nodes for the individual restriction-map, adjunct, and
normalization components, and the finite-normalization split node, because the finite
normalization and unit identity now have complete proofs and the three structural gaps
are bundled in one strictly smaller theorem. No imports were removed; every retained
import is used by the definitions or proofs.

## Where the brief, the DAG or earlier work was wrong

The initial decomposition made three separate structural sorries. They form one
independent normalization result; bundling them keeps the remaining statement strictly
below the target while avoiding duplicate interfaces.

## New nodes

- `lem-sp-proper-open-comparison-normalization`

Change record: `coord/changes/D3-proper-open-comparison-normalization.md`.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
