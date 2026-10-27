# sectionProjectionRaw

## Reason

The direct concrete expression caused a deterministic kernel timeout when proving
its invertibility in CoordinateSectionArrows. Cache the category parameters using
the generic irreducible `projectionPostcompose`. Its unfolding is the original map,
so the target meanings and all existing signatures are preserved. All added
helpers have complete proofs or concrete construction bodies. No source-library
module is edited. The definition change is submitted for independent review.

## Old

```lean
def sectionProjectionRaw (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s]
    (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) :
    ((tensor A X).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).obj M)).obj
        ((inverseImage A q).obj K) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).obj K :=
  ((projectionMap (ModuleCat.{u + 1} A) s).app M).app ((inverseImage A q).obj K) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).map
      (sectionTensorRaw A s q h M K e).hom
```

## New

```lean
def sectionProjectionRaw (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {Y X : Scheme.{u}} (s : Y ⟶ X) [HasCompactification s]
    (q : X ⟶ Y) (h : s ≫ q = 𝟙 Y)
    (M K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
    (e : M ≅ 𝟙_ _) :
    ((tensor A X).obj
      ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).obj M)).obj
        ((inverseImage A q).obj K) ⟶
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).obj K :=
  projectionPostcompose
    (sectionProjectionComponent A s q M K)
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) s).mapIso
      (sectionTensorRaw A s q h M K e))

attribute [local irreducible] projectionMap
```

The generic helper, concrete `sectionProjectionComponent`, and the proved
`sectionProjectionRaw_isIso` bridge and
`sectionProjectionRaw_isIso_of_constructibleFiniteTor` applicability theorem are in the same module and attached to its
existing node. The component cache is precisely the old projectionMap component.
This avoids repeatedly elaborating the dependent component endpoints in the
invertibility bridge. The resulting module compiled in 21.2 seconds.

## Users

The following is the complete downstream list from `tools/downstream.py Sheaf.Paper.CoordinateSectionProjection --uses sectionProjectionRaw`, including the defining module.
The declaration-use search finds only the defining module.
No downstream proof unfolds the changed definition. The canonical map, its
endpoints, and every existing statement are unchanged; no forced consumer edit
is required.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CoordinateProductPresentations` | unclaimed | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CoordinateSectionArrows` | C6 | proof filled in this delivery |
| `Sheaf.Paper.CoordinateSectionProductRecursion` | Y8 | signature and statement unchanged; no edit needed |
| `Sheaf.Paper.CoordinateSectionProjection` | unclaimed | definition-preserving cached implementation |
| `Sheaf.Paper.CoordinateZeroBaseChange` | unclaimed | signature and statement unchanged; no edit needed |

## Status

landed 20261025T205426-L-3236278 2026-10-25 (merge of deliver/C6/Sheaf.Paper.CoordinateSectionArrows)
