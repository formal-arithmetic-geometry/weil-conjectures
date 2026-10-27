## What changed

Marked `WeilConjectures.commonProjectionOpenPullbackTensor_forward` as
`STATEMENT-DISPUTED` in its declaration docstring. I restored the module unchanged
apart from that diagnostic; the theorem still has its original `sorry` because the
universal statement is false.

## Proved and sorry left

No holes were closed. The original hole
`WeilConjectures.commonProjectionOpenPullbackTensor_forward` remains, attached to
`lem-sf-common-projection-open-pullback-tensor-forward`.
No new holes were added and no theorem was split off.

## No longer needed

None. The existing `Mathlib.CategoryTheory.Functor.Currying` import is retained by
the unchanged statement. No dependency nodes or modules can be pruned while the
parent theorem still cites this forward equation.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the theorem quantifies over arbitrary morphisms `mu` and `mu'`
without a compatibility hypothesis. A concrete counterexample uses the one-object
category `SingleObj (Multiplicative Bool)` for all four categories, identity functors
and comparison isomorphisms, and the first-projection functor from a product category
for each `TA`, `TB`, `TA'`, and `TB'`. The displayed equation then reduces to `mu = mu'`.
Taking `mu = false` and `mu' = true` gives distinct endomorphisms, so the equation is
not derivable from the stated assumptions. The parent theorem uses this declaration as
if its concrete canonical comparisons supplied the missing compatibility equation; that
compatibility must be added as a hypothesis or proved for those canonical comparisons
before this generic theorem can be repaired.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CommonProjectionOpenPullbackTensorForward": "c4fcadcfda3203c53ab142b1f4225fd5ff8b7636"}, "results": {}, "time": "2026-10-28T06:24:15+0800", "transitive": 0, "version": 1}
```

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
