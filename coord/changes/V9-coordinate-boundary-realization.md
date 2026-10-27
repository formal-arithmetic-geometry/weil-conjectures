# AlgebraicGeometry.ProEtale.AffineZeroPurity.realizeBoundary

## Reason

The original concrete three-factor composite took about 30 seconds of kernel
checking; combined with the file's other definitions this exceeded the fixed
60-second compile limit. Form the same composite over generic abelian categories
inside this definition, then specialize it. All three factors, their order,
coefficients, comparison functor, source and target stay identical. No data is
chosen and no proposition is weakened. The original `@[irreducible]` stays.
The profiled revised file compiled in 51.1 seconds; profiling is removed for delivery.

## Old

```lean
@[irreducible]
def realizeBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (α : CategoryTheory.Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M) L 2) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar (ModuleCat.{u + 1} A) i).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj M)) ⟶
      (comparison A X).obj (((DerivedCategory.singleFunctor _ 0).obj L)⟦(2 : ℤ)⟧) :=
  letI := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  (DerivedCategory.singleFunctor _ 0).map
      (asIso ((lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app M)).inv ≫
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategorySingleFunctor 0).inv.app
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M) ≫
    (comparison A X).map α.hom
```

## New

```lean
@[irreducible]
def realizeBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (α : CategoryTheory.Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M) L 2) :
    (DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar (ModuleCat.{u + 1} A) i).obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj M)) ⟶
      (comparison A X).obj (((DerivedCategory.singleFunctor _ 0).obj L)⟦(2 : ℤ)⟧) :=
  let realize {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
      [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C]
      [HasDerivedCategory.{u + 1} D] (F : C ⥤ D) [F.Additive]
      [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      (K L : C) (M : D) (e : M ≅ F.obj K)
      (a : (DerivedCategory.singleFunctor C 0).obj K ⟶
        ((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧) :
      (DerivedCategory.singleFunctor D 0).obj M ⟶
        F.mapDerivedCategory.obj (((DerivedCategory.singleFunctor C 0).obj L)⟦(2 : ℤ)⟧) :=
    (DerivedCategory.singleFunctor D 0).map e.hom ≫
      (F.mapDerivedCategorySingleFunctor 0).inv.app K ≫ F.mapDerivedCategory.map a
  letI := isIso_lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)
  realize (comparisonUpperStar (ModuleCat.{u + 1} A) X) _ _ _
    (asIso ((lowerStarComparisonUpperStarBaseChange i (ModuleCat.{u + 1} A)).app M)).symm
    α.hom
```

## Users

`tools/downstream.py Sheaf.Paper.AffineSpaceCoordinateBoundaries --uses
realizeBoundary` lists eleven downstream modules and two direct mentioning modules
(the item and CoordinateProductPresentations). The table includes all of them.
The only external direct caller passes the realized arrow to
`coordinateArrowComparison`; it does not unfold it. No adaptation is required.
The construction and target meanings are unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | V9 | Own module; body expresses same composite generically before specializing. |
| Sheaf.Paper.AffineSpaceThomMap | B8 | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | F4 | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.CoordinateProductPresentations | unclaimed | Direct caller at coordinateRealizeClass; identical arrow and type; no adaptation. |
| Sheaf.Paper.CoordinateSectionArrows | unclaimed | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.CoordinateSectionProductRecursion | unclaimed | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.CoordinateSectionProjection | unclaimed | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.CoordinateTowerNormalizationInduction | K4 | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.CoordinateZeroBaseChange | unclaimed | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | U3 | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.FiniteProductReductionComparisons | unclaimed | Same signature and definitionally identical composite; no adaptation. |
| Sheaf.Paper.FiniteProductScalarPresentation | unclaimed | Same signature and definitionally identical composite; no adaptation. |

## Status

landed 20261025T124201-L-1945472 2026-10-25 (merge of deliver/V9/Sheaf.Paper.AffineSpaceCoordinateBoundaries)
