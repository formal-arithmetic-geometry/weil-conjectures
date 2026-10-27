# AlgebraicGeometry.Scheme.UnitKummer.etaleLine and proLine

## Reason

Name the two concrete underlying coefficient sheaves using ordinary definitions, so elaboration
need not repeatedly unfold scalar extension and sheafification. The definition bodies are
unchanged, and the displayed result types are the previously inferred types. This is an
interface/performance repair, with no change to the objects or the target meanings.

## Old

```lean
abbrev etaleLine (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) :=
  (Etale.RawModuleScalarComparison.forget A X).obj (finiteEtaleTateLine X m A hA)

abbrev proLine (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (X : Scheme.{u}) :=
  (forgetPro A X).obj (finiteRootProTensor A m hm hA X)
```

## New

```lean
def etaleLine (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (X : Scheme.{u}) : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.RawModuleScalarComparison.forget A X).obj (finiteEtaleTateLine X m A hA)

def proLine (A : Type (u + 1)) [CommRing A] (m : ℕ) (hm : 0 < m)
    (hA : (m : A) = 0) (X : Scheme.{u}) :
    Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  (forgetPro A X).obj (finiteRootProTensor A m hm hA X)
```

## Users

`tools/downstream.py` reports zero downstream modules and the item as the only textual user
of each declaration. The two remaining theorem statements still elaborate unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.UnitKummerTwoSiteNormalization | C2 | Same concrete coefficient sheaves. |

## Status

landed 20261025T201523-L-2560006 2026-10-25 (merge of deliver/C2/Sheaf.Paper.UnitKummerTwoSiteNormalization)
