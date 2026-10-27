## What changed

The item now assembles two named finite-model substeps. `scalar_finite_core` supplies the
finite comparison, quotient maps, transitions, and their five local formula predicates.
`scalar_finite_squares` supplies the quotient and transition square equalities. The item
combines those results into the original `scalar_finite_model` conclusion.

## Proved and sorry left

The original `scalar_finite_model` hole is closed by assembling the two strict substeps.
Two strictly simpler proof obligations remain as named statements:

- `scalar_finite_core` in `Sheaf.Paper.IsomorphismScalarFiniteCore` (blueprint:
  `lem-weil-isomorphism-scalar-finite-model-core`).
- `scalar_finite_squares` in `Sheaf.Paper.IsomorphismScalarFiniteSquares` (blueprint:
  `lem-weil-isomorphism-scalar-finite-model-squares`).

## No longer needed

No imports or declared proof dependencies were removed. The original route's generic
quotient-chain theorem remains the source route recorded by the split statements.

## Where the brief, the DAG or earlier work was wrong

The concrete coefficient maps in the item are exposed through `RingCat`, while the
available generic quotient-chain theorem is parameterized by `CommRingCat`; a direct
application therefore needs a substantial coefficient-interface bridge. The bridge is
recorded in the two strict substeps rather than hidden in an untyped proof.

## New nodes

`lem-weil-isomorphism-scalar-finite-model-core` records the finite comparisons and all
local quotient/transition formulas. `lem-weil-isomorphism-scalar-finite-model-squares`
records the two categorical square equalities from those formulas. Their DAG records and
Lean declaration records are included in this delivery.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
