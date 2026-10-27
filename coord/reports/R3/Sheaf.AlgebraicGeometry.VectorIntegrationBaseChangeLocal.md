## What changed

Added `Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalUnit`, which records the
strictly lower degree-zero local exchange equation after postcomposition with the ordinary
constant-unit pullback.  The assigned theorem now invokes this calculation and cancels the
unit comparison using `cancel_mono`.

## Proved and sorry left

Closed `AlgebraicGeometry.Etale.vectorIntegration_baseChange_local` (1 sorry).

Added one sorry in `AlgebraicGeometry.Etale.vectorIntegration_baseChange_local_unit`, the
named degree-zero exchange calculation used by the parent theorem.

## No longer needed

None.  The assigned module still needs its `VectorTraceGeometry` import and the new unit
calculation module.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted a Lean declaration for the degree-zero exchange calculation
that combines the supplied coefficient and compact-support comparison equations.  It is now
split as `lem-pur-vector-integration-base-change-local-unit`; the parent proof is the real
cancellation step from that lower statement.

## New nodes

`lem-pur-vector-integration-base-change-local-unit` —
`Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalUnit`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocal": "b852bc2b910143161f8e4109d1ddfe38d27bc16f", "Sheaf.AlgebraicGeometry.VectorIntegrationBaseChangeLocalUnit": "379b25bcb9c90872cd2752c14471cb4dbf476004"}, "results": {}, "time": "2026-10-28T06:29:47+0800", "transitive": 0, "version": 1}
```

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
