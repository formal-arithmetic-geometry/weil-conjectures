# AlgebraicGeometry.Etale.rawRestrictedDerivedPullback

## Reason

The raw derived pullback and chart class pullback used definitionally equal but
syntactically different free-sheaf abbreviations. Kernel profiling found 14.7 seconds
checking an equation between the raw pullback and its canonical free-sheaf formula,
and the complete affine descent file exceeded 60 seconds. Use the already existing
`abelianComparisonFree` abbreviation consistently in the raw pullback's source,
target and defining composite. This is the same sheafification of the same
free abelian representable. No mathematical object or target statement changes.
The old `RawRestrictedComparison.freeSheaf S U` unfolds to
`(presheafToSheaf _ _).obj (uliftYoneda.obj U ⋙ AddCommGrpCat.free)`, exactly as
`(abelianComparisonFree S).obj U` does. The defining pullback composite is unchanged. The same abbreviation is used in
the source binder of `rawRestrictedDerivedComparison_pullback` and its proof's
local free-sheaf abbreviations, avoiding conversions back to the old notation.
That theorem's proposition and visibility are unchanged up to definitional equality.

## Old

```lean
noncomputable def rawRestrictedDerivedPullback {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h).obj
        (RawRestrictedComparison.freeSheaf S U)) ⟶ K⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h').obj
        (RawRestrictedComparison.freeSheaf S U)) ⟶ K'⟦q⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
        (RawRestrictedComparison.freeSheaf S U)) ≫
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    (D+((a)^*[AddCommGrpCat.{u + 1}])).map z ≫
    ((D+((a)^*[AddCommGrpCat.{u + 1}])).commShiftIso q).hom.app K ≫
    (shiftFunctor _ q).map φ
```

## New

```lean
noncomputable def rawRestrictedDerivedPullback {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h).obj
        ((abelianComparisonFree S).obj U)) ⟶ K⟦q⟧) :
    (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h').obj
        ((abelianComparisonFree S).obj U)) ⟶ K'⟦q⟧ :=
  (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{u + 1} a h h' w.symm).hom.app
        ((abelianComparisonFree S).obj U)) ≫
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    (D+((a)^*[AddCommGrpCat.{u + 1}])).map z ≫
    ((D+((a)^*[AddCommGrpCat.{u + 1}])).commShiftIso q).hom.app K ≫
    (shiftFunctor _ q).map φ
```

The definition now publicly imports
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImageClassCompatibility`, where the
canonical free-sheaf functor is defined.

The source-binder spelling in the naturality theorem changes as follows.

Old:
```lean
theorem rawRestrictedDerivedComparison_pullback {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h).obj
        (RawRestrictedComparison.freeSheaf S U)) ⟶ K⟦q⟧) :
    rawRestrictedDerivedCohomologyPullback a h h' w K K' φ q U
        (rawRestrictedDerivedComparison h q K U z) =
      rawRestrictedDerivedComparison h' q K' U
        (rawRestrictedDerivedPullback a h h' w K K' φ q U z)
```

New (definitionally equal):
```lean
theorem rawRestrictedDerivedComparison_pullback {S Y Y' : Scheme.{u}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h')
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (K' : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (φ : (D+((a)^*[AddCommGrpCat.{u + 1}])).obj K ⟶ K')
    (q : ℤ) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} h).obj
        ((abelianComparisonFree S).obj U)) ⟶ K⟦q⟧) :
    rawRestrictedDerivedCohomologyPullback a h h' w K K' φ q U
        (rawRestrictedDerivedComparison h q K U z) =
      rawRestrictedDerivedComparison h' q K' U
        (rawRestrictedDerivedPullback a h h' w K K' φ q U z)
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.RawRestrictedDerivedComparisonPullback
--uses rawRestrictedDerivedPullback` lists the existing modules below. The source
module is unclaimed in the supplied claim snapshot. The existing naturality theorem's source binder and its local free-sheaf
abbreviations use the same canonical notation. These are definitionally equal
replacements, and no other existing module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawRestrictedDerivedComparisonPullback | unclaimed | The free-sheaf abbreviation in this definition is aligned with the chart API; its naturality theorem has the identical proposition using the canonical free-sheaf abbreviation. |
| Sheaf.AlgebraicGeometry.CartesianPresentationShiftCoherence | unclaimed | Imports the module but does not mention the changed definition; all declarations retain their meaning. |
| Sheaf.AlgebraicGeometry.RawFixedDerivedComparisonNaturality | new in A2 | Uses the same raw pullback with canonical free-sheaf sources. |
| Sheaf.AlgebraicGeometry.RawDerivedClassAffineDescent | A2 | Its final transport equation uses the canonical formula without repeated free-sheaf conversion. |

The identity
`RawRestrictedComparison.freeSheaf S U = (abelianComparisonFree S).obj U`
was checked by `rfl`. The original downstream
`CartesianPresentationShiftCoherence` compiled unchanged against the adjusted
module in 3.0 seconds.

Because the replacement is definitionally equal, every downstream target retains
exactly its original meaning. There are no forced adaptations of another group's
module.

## Status

landed 20261015T154148-L-157560 2026-10-15 (merge of deliver/A2/Sheaf.AlgebraicGeometry.RawDerivedClassAffineDescent)
