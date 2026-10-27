## What changed

Restored `Sheaf.Paper.CommonProjectionOpenPullbackTensor` with a complete proof of
`commonProjectionOpenPullbackTensor`. The proof unfolds the displayed predicate,
uses a generic categorical inverse-square cancellation lemma, and applies the
strictly smaller forward compatibility equation. Added the forward equation as a
separate split theorem in `Sheaf.Paper.CommonProjectionOpenPullbackTensorForward`.

## Proved and sorry left

Closed `commonProjectionOpenPullbackTensor` (1 of 1 original sorry). Added one
strictly smaller sorry theorem, `commonProjectionOpenPullbackTensor_forward`,
which is the forward representative equation used by the cancellation proof.

## No longer needed

None. The imported tensor-comparison definition and the operation-stage data are
used by the forward statement and the inverse proof.

## Where the brief, the DAG or earlier work was wrong

The quarantined file imported `Sheaf.Paper.CommonProjectionTensorComparison`,
which was itself quarantined by the build rework and made the module fail with a
bad-import error. The delivery restores the dependency through a new forward
compatibility module in the same item sandbox.

## New nodes

`lem-sf-common-projection-open-pullback-tensor-forward` records the forward
compatibility equation left as the remaining proof obligation.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonProjectionOpenPullbackTensor": "1275cfb8aa39624d10b38dc74a3d10efa8165760", "Sheaf.Paper.CommonProjectionOpenPullbackTensorForward": "f1a0cf609dbfe6c7bcea2d34d580d63da7149683"}, "results": {"Sheaf.Paper.CommonProjectionOpenFactor": {"hash": "4cf371e297086bc41308917f63783e452bad0ba1", "status": "OK"}}, "seconds": 51, "time": "2026-10-28T02:07:07+0800", "transitive": 0, "version": 1}
```

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
