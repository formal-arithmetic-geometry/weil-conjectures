## What changed

Added `Sheaf.Paper.ScalarTowerTensorLimitSquareTransport`, which isolates the
localization and total-limit transport from an arbitrary strict `DerivedSigmaModel`
comparison. The item now obtains the canonical `derivedSigma` normalization from
`derivedSigma_existsUnique` and applies this transport theorem. The item imports
that proof-only module.

## Proved and sorry left

The original `scalarTowerTensorLimitSquare` sorry is closed by applying the new
transport statement and the existing canonical normalization witness. One strictly
simpler sorry remains in
`WeilConjectures.ScalarExtensionTower.scalarTowerTensorLimitSquare_of_derivedSigmaModel`
(node `stage3-pur-scalar-tensor-limit-transport`); it is the localization and
limit passage after the finite strict equation has been supplied as `DerivedSigmaModel`.
No definition contains a sorry.

## No longer needed

The item no longer directly needs the six low-level proof dependencies from its
old plan: they are used by the split transport node instead. No declaration or
module outside this delivery is withdrawn, and the unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the strict quotient tensor calculation and the
localization/total-limit transport into one theorem. The imported API contains
the strict comparison only as `DerivedSigmaModel`; the missing transport is a
separate, strictly smaller argument. The node copy records this decomposition.

## New nodes

`stage3-pur-scalar-tensor-limit-transport` records the strict-to-limit transport
substep and is stated in `Sheaf.Paper.ScalarTowerTensorLimitSquareTransport`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ScalarTowerTensorLimitSquare": "719e0d24cb34db4aa8ec61688f72dcaaa8468039", "Sheaf.Paper.ScalarTowerTensorLimitSquareTransport": "a65317d84d0c0eea91649461e37d0e7766917682"}, "results": {}, "time": "2026-10-28T02:34:05+0800", "transitive": 0, "version": 1}
```

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
