## What changed

Restored the module's explicit dependency on
`WeilConjectures.SixFunctors.ProEtale.ScalarExtension` in the sandbox copy.  The
existing theorem statement and its existing proof placeholder are unchanged.
This keeps the scalar-extension declarations available while the quarantined
`Sheaf.Paper.EtaleFiniteCoefficientHomArrow` dependency is rebuilt.

## Proved and sorry left

No theorem holes were closed.  The existing `finiteHomIntrinsic_tensorComposition`
sorry remains, matching the assigned rework baseline.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The global build record reported a bad import of
`Sheaf.Paper.EtaleFiniteCoefficientHomArrow` while that dependency was
quarantined during rework.  The module itself was restored unchanged; this
delivery records the explicit upstream scalar-extension dependency needed by
its current import closure.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteHomIntrinsicTensorComposition": "77dc0ca24c3820d211f902a495ef1129f9df3313"}, "results": {}, "time": "2026-10-28T00:47:26+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
