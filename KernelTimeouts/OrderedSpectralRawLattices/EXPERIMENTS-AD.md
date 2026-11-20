# DefEq Internal Cost Experiments

Case: `OrderedSpectralRawLattices`
Lean: 4.35.0 (`f4946fdb6b6` source snapshot on the current 4.35.0 tree)
Root: final conversion from `exists_stratified_lisse_integral_lattice` to `RawStratifiedLattices`.

## A1: Three-route bundle alignment

`original.lean` reproduces the 40.23 s deterministic timeout. The first two `continuousMapRingObj` values use competing regular, Henselian, and domain instance routes. The all-route control `aligned-all-routes.lean` disables all three routes and completed in 16.91 s (27.55 s user, 0.81 s system, 2,538,468 KB RSS). `all-routes-head.lean` confirms that both ring-object values become syntactically equal; the third map and folded predicate still differ.

Single-route and two-route restorations all remain timeouts (the measured matrix is 44.93--45.53 s; round-two restoration diagnostics fail after the private theorem is unavailable). The complete bundle is therefore the valid ablation/restoration unit. No one route is a valid isolated target.

## B: Shared-provider test

Rejected as invalid. The imported helper theorem has its instance arguments already elaborated, while local instance availability changes only the newly elaborated goal. A shared local provider would change the stored theorem/consumer pair or the dependent lattice predicate. No B0/B1/B2 three-way construction preserves the exact type, consumer, and root obligation. The source matrix is evidence for a bundle trigger, not a shared-object timing experiment.

## C: Dependent bundle test

Rejected as invalid for the same reason. Adding a wrapper or repeated field that is not consumed does not alter the root; rebuilding the theorem changes the target. The existing eight-row instance matrix cannot attribute cost to a binder or field. No C timing is claimed.

## Conclusion

The measurable result is A1: a complete three-route source alignment removes the timeout-scale comparison, while every partial restoration fails. B and C are explicitly invalid under the exact-consumer requirement; forcing synthetic providers would not answer the assigned question.

## READY2 round 2

The READY2-4.35.0 original trace root was 51.962 s with 18,944,709 calls, 51.938 s comparison-exclusive time, and 24 ms reduction-exclusive time. Dependent comparison/reduction was 51.764 s / 4 ms; 2,928,324 instantiations were recorded. The Expr proxy created 213,249,957 expressions / 6,975,943,792 bytes, with a 955,973,632-byte RSS/commit delta.

The dominant path was `root/binder_body[17]` through nested `Exists` and `Quiver.Hom` comparisons into `Functor.obj`/`Mod.X`, with 51,909 ms in the `Quiver.Hom` subtree. The all-route alignment entered no root over 100 ms (2,641,796 KB RSS). Restoring only the domain or regular route returned 35.939 s / 36.282 s roots with about 18.945M calls and 213.25M Expr constructions; the Henselian variants failed at the deterministic timeout before a comparable final root. The complete R/H/D bundle remains the only valid ablation unit.
