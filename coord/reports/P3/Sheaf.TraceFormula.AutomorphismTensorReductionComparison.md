## What changed

Copied and edited `Sheaf.TraceFormula.AutomorphismTensorReductionComparison`. The arbitrary
sequence-site coefficient-component naturality theorem is now proved by factoring every
arrow into a fixed-level vertical arrow and a quotient-index horizontal arrow. The two
componentwise clauses are recorded as named split theorems. No imports were added or removed.

## Proved and sorry left

Proved `trfAutomorphismCoefficientComponent_naturality` (one original sorry closed).
The following named statements remain sorry and are represented by the new DAG nodes listed
below:

- `trfAutomorphismCoefficientComponent_vertical`;
- `trfAutomorphismCoefficientComponent_horizontal`;
- `trfAutomorphismTensorEvaluation` (the original tensor-slice comparison).

No definition contains a sorry.

## No longer needed

None. The proof uses the existing site, coefficient, and inverse-image declarations, and the
new vertical and horizontal component clauses.

## Where the brief, the DAG or earlier work was wrong

The original proof boundary left the arbitrary-arrow naturality clause as one opaque hole.
The Lean proof exposes the required factorization into vertical and horizontal clauses. The
finite tensor evaluation clause remains open because its slice sheafification comparison is
not definitionally identical to the finite raw transport.

## New nodes

- `lem-trf-automorphism-coefficient-component-vertical`: fixed-level vertical naturality.
- `lem-trf-automorphism-coefficient-component-horizontal`: arbitrary quotient-index horizontal
  naturality.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
