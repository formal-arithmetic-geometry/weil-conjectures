# AlgebraicGeometry.Scheme.UnitKummer.proCohomologyPullback

## Reason

Write the previously inferred result type explicitly, preserving the exact type and body. This keeps elaboration of the large sheaf cohomology instances predictable. Every target and theorem retains its original meaning. This is an interface/performance repair in the assigned Sheaf module; no adopted source-library declaration changes.

## Old

```lean
@[irreducible] def proCohomologyPullback {X Y : Scheme.{u}} (v : Y ⟶ X)
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) (q : ℕ) :=
  Sheaf.H.mapFunctor (ProEtale.upperStar AddCommGrpCat.{u + 1} v)
    ((constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} v).symm.app
      (AddCommGrpCat.of (ULift ℤ))) F q
```

## New

```lean
@[irreducible] def proCohomologyPullback {X Y : Scheme.{u}} (v : Y ⟶ X)
    (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H F q →+ Sheaf.H
      ((ProEtale.upperStar AddCommGrpCat.{u + 1} v).obj F) q :=
  Sheaf.H.mapFunctor (ProEtale.upperStar AddCommGrpCat.{u + 1} v)
    ((constantSheafCompUpperStarIso AddCommGrpCat.{u + 1} v).symm.app
      (AddCommGrpCat.of (ULift ℤ))) F q
```

## Users

`python3 tools/downstream.py Sheaf.Paper.UnitKummerTwoSiteNormalization --uses proCohomologyPullback`
reports no downstream modules and only the item itself as a textual user. The normalization and frame-normalization statements still elaborate in this packet. No target statement changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.UnitKummerTwoSiteNormalization | C2 | Same objects and maps; statements retain their original meaning. |

## Status

landed 20261025T201523-L-2560006 2026-10-25 (merge of deliver/C2/Sheaf.Paper.UnitKummerTwoSiteNormalization)
