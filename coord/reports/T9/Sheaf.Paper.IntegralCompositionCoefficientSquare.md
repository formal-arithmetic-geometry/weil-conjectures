## What changed

Repaired the rework import boundary in `lean/Sheaf/Paper/IntegralCompositionCoefficientSquare.lean`.
The module retains its two required public imports and now explicitly re-exports the
three restored ancestor modules (`QcqsCompactSupportRealization`,
`CompactSupportFiniteAction`, and `IntegralScalarExtensionConstructibleIntrinsic`).
This keeps the dependency closure available while the rework cluster is rebuilt,
preventing the prior global-build `bad import` failures. The theorem signature and
body remain unchanged. The repaired module compiles with `lcompile.py`.

## Proved and sorry left

The module still has one existing sorry,
`WeilConjectures.sfIntegralComposition_coefficient_comm`, node
`lem-zl-integral-composition-coefficient-square`. No new sorries were added and no
definition contains sorry.

## No longer needed

None. The two direct imports remain required by the theorem signature; the three
explicit ancestor imports are required to keep the restored dependency closure
available during rework builds.

## Where the brief, the DAG or earlier work was wrong

The 2026-10-27 global-build record reported both direct imports as unavailable because
their ancestor modules were missing from the active build closure. The current
sources compile, and the explicit ancestor imports repair that closure without
changing any declaration or DAG statement.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralCompositionCoefficientSquare": "b719d2ba408bfcf7da1ca77a52e46534089db02f"}, "results": {"Sheaf.Paper.FieldShriekCompositionCoefficientSquare": {"hash": "85e05ba9602b966d1b7ea6e6a6df2784b86370a1", "status": "OK"}}, "seconds": 105, "time": "2026-10-28T00:51:37+0800", "transitive": 0, "version": 1}
```

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
