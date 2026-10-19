## What changed

Proved `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq` in
`lean/WeilConjectures/ZetaFunction/TraceFormula.lean`. The proof imports
`WeilConjectures.WeilSheaf.LowerShriekOperations` and applies
`AlgebraicGeometry.WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction`,
converting `1 ≤ m` to the required `m ≠ 0` by `omega`. No statement or definition changed.

## Proved and sorry left

Closed the `sorry` in `AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq`.
No `sorry`s were added; the module has no `sorry`s left.

## No longer needed

No proof imports or DAG nodes were removed. The existing imports remain necessary for the other
proofs in the module; `WeilConjectures.WeilSheaf.LowerShriekOperations` is needed for the new
trace-formula application.

## Where the brief, the DAG or earlier work was wrong

The source-library theorem used by the proof is the direct `WeilComplex` trace identity in
`LowerShriekOperations`; no new common-stage coefficient theorem is needed for this Lean
specialization. No DAG statement was changed.

## New nodes

None.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
