## What changed

Closed the `rationalDualizing_identification` theorem. The proof constructs the integral
coefficient object `U`, obtains the integral exceptional comparison, lifts it to the
constructible category, and then composes its rational localization with the right
component of `S.fields.rationalizationComparison`. The defining equality between
`rationalization U` and `coefficientUnit` finishes the required `DualizingIdentification`.

Added `Sheaf.SixFunctors.IntegralDualizingExceptionalUnitBridge`, a strictly simpler
integral-stage comparison theorem. It isolates the integral exceptional-unit step so
the rational theorem does not import the cyclic paper module.

## Proved and sorry left

- Proved `WeilConjectures.RationalOperations.rationalDualizing_identification` (the
  module's original one `sorry` is closed).
- Added one strictly simpler statement-only theorem,
  `WeilConjectures.RationalOperations.integralDualizing_exceptional_unit_bridge`,
  with its proof left as `sorry`. Its DAG node is
  `lem-sf-rational-dualizing-identification-integral-bridge`.

## No longer needed

The implemented route does not use the original planned proof dependencies
`def-weil-integral-rational-qbar-compact-support`, `def-weil-exceptional-inverse-image`,
`def-weil-derived-pullback-tensor-hom`, or `thm-coef-rational-verdier` directly. The
bridge and the existing `RationalOperationsData` interfaces provide the needed
integral comparison and rationalization component. No imports outside the item and
its new bridge were changed.

## Where the brief, the DAG or earlier work was wrong

The prior route attempted to obtain the integral exceptional-unit comparison through
`Sheaf.Paper.IntegralDualizingExceptionalUnit`, which imports the rational operations
module and creates an import cycle. The integral comparison is therefore split into a
separate bridge theorem with a smaller statement and an independent module.

## New nodes

- `lem-sf-rational-dualizing-identification-integral-bridge` in
  `dag/nodes/sec-six-functors/lem-sf-rational-dualizing-identification-integral-bridge.json`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralDualizingExceptionalUnitBridge": "ed09bbd61d459bbfe7d982c5e140af7828379aa2", "Sheaf.SixFunctors.RationalDualizingIdentification": "8bb3207e9be05e516b7361a4585430d9e198193c"}, "results": {"Sheaf.SixFunctors.CoefQbarVerdierDualizing": {"hash": "cd16b4af6d8c1a630d26dd9de7b846da0c3f90f8", "status": "OK"}, "Sheaf.SixFunctors.RationalOperations": {"hash": "4e2dd58b9d060b7498c0e0a39f8083bc1e768c81", "status": "OK"}}, "seconds": 63, "time": "2026-10-28T01:20:39+0800", "transitive": 0, "version": 1}
```

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
