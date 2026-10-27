# CategoryTheory.partitionModuleRings

## Reason

Repeated elaboration of the reducible ring-sheaf abbreviation causes large definitional-equality
checks, especially in the derived-category statements. Keep the canonical Mathlib construction
as an ordinary transparent definition; give evaluation its explicit module-universe type.
No mathematical object, data, hypothesis, or conclusion changes.

Replace the unused public import
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions` by
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective`. The latter supplies the
`IsKInjective` predicate in the unchanged resolution theorem. The proof uses the
universal property in Mathlib directly and does not choose any resolution-derived pair.
No downstream module imports this item, so there is no consumer of its former re-export.

## Old

```lean
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions

abbrev partitionModuleRings (O : Sheaf J.toGrothendieck CommRingCat.{max u v w}) :=
  (sheafCompose J.toGrothendieck
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj O

abbrev partitionModuleEvaluation
    (O : Sheaf J.toGrothendieck CommRingCat.{max u v w}) (W : C) :=
  SheafOfModules.evaluation.{max u v w} (partitionModuleRings J O) (op W)
```

## New

```lean
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective

def partitionModuleRings (O : Sheaf J.toGrothendieck CommRingCat.{max u v w}) :=
  (sheafCompose J.toGrothendieck
    (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).obj O

abbrev partitionModuleEvaluation
    (O : Sheaf J.toGrothendieck CommRingCat.{max u v w}) (W : C) :
    ringedSiteModules.{max u v w} (partitionModuleRings J O) ⥤
      ModuleCat.{max u v w} ((partitionModuleRings J O).obj.obj (op W)) :=
  SheafOfModules.evaluation.{max u v w} (partitionModuleRings J O) (op W)
```

## Users

`tools/downstream.py` reports zero downstream modules for both declarations. Searches of
`lean/Sheaf` and `lean/WeilConjectures` find only this item; no consumer adaptation is needed.
Neither construction is used by any locked target statement.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.PartitionModuleEvaluation | S2 | All statements retain their meaning; proof elaboration uses the shared ring-sheaf definition. |

## Status

landed 20261025T101321-L-3682330 2026-10-25 (merge of deliver/S2/Sheaf.CategoryTheory.PartitionModuleEvaluation)
