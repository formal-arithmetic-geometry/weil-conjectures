## What changed

Filled the two theorem proofs in
`lean/Sheaf/CategoryTheory/Triangulated/TExactCohomologyBoundaryComparison.lean`:
`texact_cohomology_boundary_comparison` is proved by the shift coherence identity,
naturality of the degree-zero comparison, and functoriality of `homology₀`; the theorem
`texact_cohomology_boundary_comparison_naturality` is proved from
`homologySequenceδ_naturality` and naturality of the comparison natural isomorphisms.
No definitions, declarations, signatures, imports, or node records were changed.

## Proved and sorry left

Both previous holes are closed: `texact_cohomology_boundary_comparison` and
`texact_cohomology_boundary_comparison_naturality`. The module has zero `sorry`s left,
and the delivery adds no holes.

## No longer needed

None. The existing public imports and all recorded dependency nodes remain needed by the
proof and were retained.

## Where the brief, the DAG or earlier work was wrong

None found. The completed proof follows the recorded six-step argument and preserves both
statements exactly.

## New nodes

None.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
