## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq`
with the existing library declaration
`AlgebraicGeometry.WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction`,
using `omega` to turn `1 ≤ m` into `m ≠ 0`. Added its proof-only import
`WeilConjectures.WeilSheaf.LowerShriekOperations`. The two Frobenius expressions
are definitionally equal. Every signature, definition, existing docstring and
public import is unchanged. Single-file compilation succeeded without warnings
in 11.6 seconds.

This consolidates an existing duplicate trace-formula obligation; it does not
supply an independent proof of the trace formula. The canonical declaration
in `LowerShriekOperations` already existed and remains open. No new theorem or
hole is introduced. The already completed constant-sheaf, proper comparison and
finite-range specialization proofs in this module are unchanged.

## Proved and sorry left

Closed 1 of 1 local holes:
`AlgebraicGeometry.WeilComplex.finsum_trace_compactlySupportedCohomology_eq`
(blueprint `thm-trf-grothendieck-lefschetz-qbar`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered module.
The existing, unchanged canonical dependency
`AlgebraicGeometry.WeilComplex.sum_trace_compactlySupportedCohomology_eq_sum_traceFunction`
(blueprint `thm-trf-grothendieck-lefschetz-qbar`) still contains its original
`sorry`. This delivery closes the duplicate wrapper, rather than proving that
dependency. In particular its transitive axiom set still contains `sorryAx`.

## No longer needed

No imports or modules removed. No DAG dependency is withdrawn: the canonical
trace formula retains its mathematical proof obligation and the existing
specialization route for `prop-every-iterate-trace` is unchanged. Repeating the
trace-formula proof in this module is unnecessary because the same statement
already exists in `WeilConjectures.WeilSheaf.LowerShriekOperations`.

## Where the brief, the DAG or earlier work was wrong

The assigned module contains a duplicate of the existing compact-support trace
formula. Its hypothesis `1 ≤ m` is equivalent to the existing theorem's
`m ≠ 0`, and `frobeniusEnd` is definitionally `frobenius.toLinearMap`.
No statement repair is needed. The only direct `lean.module` attachment to this
module is `prop-every-iterate-trace`, whose final finite-range theorem is
already proved; the remaining hole is the earlier general trace-formula wrapper.
Searches through leanfinder, loogle and the launcher grep were recorded in
`searches.jsonl`; direct `rg` located the exact library theorem. The import-cycle
check permits the proof-only import. No DAG route or unit step changes.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
