## What changed

Added the generic categorical transport module
`Sheaf.Paper.DiagonalTraceRootProjectionTransport`.  Its theorem isolates the
shift, finite-projection, and strict-root-system transport calculation for an
arbitrary exact functor and system-valued exact functor.  The assigned theorem
now specializes this result to the completed diagonal restriction and the
coefficient line cone; the specialization is a complete Lean proof and leaves
the target statement unchanged.  The target node records the new proof
dependency and the new transport node records the remaining intermediate
calculation.

## Proved and sorry left

`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_rootProjection` is
proved from the generic transport theorem (one original `sorry` closed).

The generic theorem
`AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_shiftedRootProjection_transport`
remains as one named `sorry`.  It is strictly more general and is the
unproved categorical transport subargument, with its source and proof plan in
its docstring and DAG node.

## No longer needed

The attempted proof import of
`Sheaf.Paper.DiagonalTraceCoefficientProjection` was removed: the specialization
uses only the definitions already provided by `DiagonalTowerTraceCoefficients`,
`DiagonalTraceRootTransport`, and the new generic transport theorem.  No other
planned dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof description treats the shifted strict-root transport and
finite projection as a single elementary step.  Its direct categorical glue is
substantial, so it was split into the generic transport theorem above; the
coefficient theorem is now a direct specialization.  No mathematical statement
was changed.

## New nodes

- `lem-sfb-diagonal-trace-shifted-root-projection-transport`: generic shifted
  root-projection transport, module
  `Sheaf.Paper.DiagonalTraceRootProjectionTransport`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceRootProjection": "9df800ff6193450f83a60007e5f9d678e0c81eab", "Sheaf.Paper.DiagonalTraceRootProjectionTransport": "14c237017344a7cde8fe39b7f103a0dd8cf3f4e2"}, "results": {}, "time": "2026-10-28T08:06:30+0800", "transitive": 0, "version": 1}
```

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
