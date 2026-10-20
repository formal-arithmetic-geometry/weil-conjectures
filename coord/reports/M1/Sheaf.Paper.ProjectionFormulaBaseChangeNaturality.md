## What changed

Filled the proof of `AlgebraicGeometry.Scheme.proEtaleProjectionFormula_baseChange`.
The proof instantiates `projectionMate_square_of_tensor_coherence_projection` with the
four pro-etale pullback/direct-image adjunctions, the canonical tensor comparisons, and
the ambient pullback comparison. Its tensor coherence hypothesis is discharged by
`proEtaleProjectionFormula_tensor_coherence`.

## Proved and sorry left

Closed the sole `sorry` in the item module, `AlgebraicGeometry.Scheme.proEtaleProjectionFormula_baseChange`.
No sorries were added.

## No longer needed

No imports or DAG dependencies were removed. The proof uses the existing mate-square
coherence and pro-etale tensor-coherence declarations already imported by the module.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was accurate. The final theorem is a direct specialization of the
existing abstract mate-square coherence theorem; no statement changes were needed.

## New nodes

None.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
