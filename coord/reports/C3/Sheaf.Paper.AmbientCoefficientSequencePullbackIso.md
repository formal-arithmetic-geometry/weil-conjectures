## What changed

Added `Sheaf.Paper.AmbientCoefficientSequencePullbackIsoApp` with the componentwise
sequence-site comparison as a named intermediate theorem, and proved the assigned
`coefficientPullback_none_isIso` by applying that theorem at every site object and
reflecting isomorphisms through the sheaf-to-presheaf functor. The item imports the
new intermediate module as a proof-only import.

## Proved and sorry left

The assigned theorem `WeilConjectures.AmbientPullbackTensor.coefficientPullback_none_isIso`
is proved. One strictly smaller intermediate theorem remains sorry:
`WeilConjectures.AmbientPullbackTensor.coefficientPullback_none_isIso_app`, node
`lem-sf-ambient-coefficient-pullback-iso-sequence-app`.

## No longer needed

No imports from the assigned module were removed. The proof uses only
`AmbientPullbackSiteData` and the new componentwise theorem; the original finite-stage
module is used by the new theorem's DAG plan but is not imported directly here.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan omitted the componentwise theorem needed to express the
finite-stage comparison on product-site objects. The missing statement was split off
as a strictly simpler componentwise obligation.

## New nodes

`lem-sf-ambient-coefficient-pullback-iso-sequence-app` owns the componentwise theorem
and is implemented by `Sheaf.Paper.AmbientCoefficientSequencePullbackIsoApp`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AmbientCoefficientSequencePullbackIso": "bd93843a120fadf4480908a3675d325d703fa076", "Sheaf.Paper.AmbientCoefficientSequencePullbackIsoApp": "e8c3d7d2027d6b79cd9528dfd0d31d217cc90fa1"}, "results": {}, "time": "2026-10-28T09:27:54+0800", "transitive": 0, "version": 1}
```

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
