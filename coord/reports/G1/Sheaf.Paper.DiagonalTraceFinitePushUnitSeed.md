## What changed

The change record is `coord/changes/diagonal-trace-finite-push-unit-seed.md`.

Added the pre-varying common-unit comparison theorem in
`Sheaf.Paper.DiagonalTraceFinitePushUnitCommon`.  The target theorem now imports it,
composes with the varying isomorphism, and closes by functoriality and the
inverse-hom identity.  The sandbox compiles both modules.

## Proved and sorry left

- Proved `diagonalTrace_finitePush_unit_seed`.
- Added one strictly smaller split theorem, with `sorry`:
  `diagonalTrace_finitePush_unit_common`.

## No longer needed

- Removed the exploratory proof-only import `Sheaf.Paper.DiagonalTraceCoefficientProjection`
  from the target module.
- The target proof no longer directly needs the original exact-square, coefficient,
  presentation, and tower-diagonal proof dependencies; those are delegated to the
  pre-varying split theorem and its node.

## Where the brief, the DAG or earlier work was wrong

The direct expansion route exposed incompatible derived-category instances when
rewriting the completed and limit normalizations in the target module.  The DAG's
pre-varying common-unit step is therefore recorded as a separate theorem, while the
remaining target proof is the explicit varying-isomorphism transport.

## New nodes

- `lem-sfb-diagonal-trace-finite-push-unit-common`, for
  `Sheaf.Paper.DiagonalTraceFinitePushUnitCommon.diagonalTrace_finitePush_unit_common`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalTraceFinitePushUnitCommon": "6eb89ad1435e7e61e565efb74cdacde98f149ede", "Sheaf.Paper.DiagonalTraceFinitePushUnitSeed": "141713c36107b03a2bfc155b4e8395329541a928"}, "results": {"Sheaf.Paper.DiagonalTraceFinitePushUnit": {"hash": "ed3641474c9e6206ed4e382d6b355f1a04a22918", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T08:32:39+0800", "transitive": 0, "version": 1}
```

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
