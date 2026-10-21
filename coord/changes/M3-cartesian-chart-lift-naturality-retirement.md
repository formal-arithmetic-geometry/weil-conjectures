# Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality

## Reason

Retire the duplicate listed in `coord/retire-items.tsv`, under the human-approved
retirement recorded in `coord/changes/retire-sheaf-twins-20261020.md`.
The adopted upstream module already proves exactly the same public theorem.
The two signatures agree token for token when whitespace is ignored.
The current source and quarantine have no import of the Sheaf copy; downstream.py
also reports zero downstream modules. The upstream consumer
`WeilConjectures.AlgebraicGeometry.CartesianRawClassChartNaturality` already imports
`WeilConjectures.AlgebraicGeometry.CartesianChartLiftNaturality` and applies its theorem.
Thus retirement introduces no new import environment or pair of duplicate modules.

The historical M3 return describes a proposed change to chart-class pullback
which is absent from current source. This delivery does not restore that old
packet. Both the original definition and its raw affine-descent consumer remain
unchanged and are checked against the current upstream implementation.

## Old

The Sheaf module publicly states and proves:

```lean
theorem cartesianChartCohomologyLift_naturality
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (j : I) (W : (D.obj j).left.Etale) (V : c.pt.left.Etale)
    (r : V.left ⟶ W.left)
    (hr : IsPullback r V.hom W.hom (c.π.app j).left)
    (l m : Over j) (a : m ⟶ l)
    (x : restrictedOverCohomology (pullback.snd f (D.obj j).hom)
      (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D j).obj l) W) :
    cartesianChartCohomologyLift f D c F q j W V r hr l x ≫
      (shiftFunctor _ (q : ℤ)).map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
          (c.π.app m.left).left (D.map a.left).left (c.π.app l.left).left
          (congrArg (fun t ↦ t.left) (c.w a.left)).symm).hom.app _ ≫
          (D+(((c.π.app m.left).left)^*[AddCommGrpCat.{u + 1}])).map
            (cartesianDerivedImageMap f (D.obj l.left).hom (D.obj m.left).hom
              (D.map a.left).left (Over.w (D.map a.left)).symm
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) =
      cartesianChartCohomologyLift f D c F q j W V r hr m
        (restrictedOverCohomologyMap (pullback.snd f (D.obj j).hom)
          (((pullback.fst f (D.obj j).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
          (q : ℤ) ((cartesianChartDiagram f D j).map a) W x) := by
```

It additionally publicly imports `Sheaf.AlgebraicGeometry.CartesianChartLiftCoherence`
and privately imports `Sheaf.AlgebraicGeometry.CartesianChartDiagramMap` and
`Sheaf.AlgebraicGeometry.CartesianChartLiftRawNaturality` for its alternative proof.

## New

Withdraw `lean/Sheaf/AlgebraicGeometry/CartesianChartLiftNaturality.lean` through
`deleted.txt`. The existing upstream declaration with the identical signature
above and its complete proof remain verbatim in
`WeilConjectures.AlgebraicGeometry.CartesianChartLiftNaturality`.
There are no consumer edits and no changes to definitions, target statements,
unit routes, upstream signatures, attributes or public imports.

No DAG node or unit record refers to the withdrawn module or its blueprint tag
`lem-sc-cartesian-chart-lift-naturality`, so no node attachment or parent dependency
needs migration. The mathematical transition argument is retained by the upstream
consumer's existing application of the same theorem.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality | M3 | Withdraw duplicate. |
| WeilConjectures.AlgebraicGeometry.CartesianChartLiftNaturality | unclaimed | Unchanged complete replacement proof; validation only. |
| WeilConjectures.AlgebraicGeometry.CartesianRawClassChartNaturality | unclaimed | Existing caller already uses upstream theorem; validation only. |
| WeilConjectures.AlgebraicGeometry.RawDerivedClassAffineDescent | unclaimed | Historical failed consumer checked unchanged; validation only. |

There are zero direct or transitive importers of the withdrawn module in current
library source, and no quarantined importer. No held module is adapted.

Validation: the published replacement's axiom check reports only `propext`,
`Classical.choice`, and `Quot.sound`; the upstream caller and historical failed
consumer compile unchanged in 9.9 and 33.7 seconds. Recompiling the entire unchanged
upstream proof source separately hit the file time limit; this delivery changes
none of that source and uses its published artifact.

## Status

landed 20261021T003513-L-1644761 2026-10-21 (merge of deliver/M3/Sheaf.AlgebraicGeometry.CartesianChartLiftNaturality)
