# Sheaf.Paper.IntegralRegularCoefficientPullback

## Reason

Expose the two existing naturality-square lemmas so the coefficient-transport proof can use them. Their statements, proofs, and all definitions are unchanged. This reuses the existing calculations rather than duplicating them in the transport module.

Both the original and changed module are checked against current shared sources. This module is unclaimed. No target statement or target-used definition changes meaning; no target statement review is reopened. Zero ranks and empty schemes remain covered.

## Old

```lean
private theorem conjugated_morphism_square
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) {A B : C} {R S : D}
    (eX : R ⟶ S) [IsIso eX] (eY : A ⟶ B) [IsIso eY]
    (ηf : R ⟶ G.obj A) (δ : S ⟶ G.obj B) (p : R ⟶ R) (q : A ⟶ A)
    (hs : ηf ≫ G.map eY = eX ≫ δ) (hp : p ≫ ηf = ηf ≫ G.map q) :
    δ ≫ G.map (inv eY ≫ q ≫ eY) = (inv eX ≫ p ≫ eX) ≫ δ

private theorem continuous_function_unit_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O]
    (p : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X O) ⟶
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X O))
    (q : (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf Y O) ⟶
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf Y O))
    (h : continuousFunctionPushforward f O ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map q = p ≫ continuousFunctionPushforward f O)
    (y : Y) :
    ((q.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down y =
      ((p.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down (f y)
```

## New

```lean
theorem conjugated_morphism_square
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (G : C ⥤ D) {A B : C} {R S : D}
    (eX : R ⟶ S) [IsIso eX] (eY : A ⟶ B) [IsIso eY]
    (ηf : R ⟶ G.obj A) (δ : S ⟶ G.obj B) (p : R ⟶ R) (q : A ⟶ A)
    (hs : ηf ≫ G.map eY = eX ≫ δ) (hp : p ≫ ηf = ηf ≫ G.map q) :
    δ ≫ G.map (inv eY ≫ q ≫ eY) = (inv eX ≫ p ≫ eX) ≫ δ

theorem continuous_function_unit_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    (O : Type) [TopologicalSpace O] [Ring O] [IsTopologicalRing O]
    (p : (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X O) ⟶
      (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X O))
    (q : (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf Y O) ⟶
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf Y O))
    (h : continuousFunctionPushforward f O ≫
      (ProEtale.lowerStar Ab.{u + 1} f).map q = p ≫ continuousFunctionPushforward f O)
    (y : Y) :
    ((q.hom.app (op (Scheme.ProEt.mk (𝟙 Y)))) (ULift.up 1)).down y =
      ((p.hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down (f y)
```

## Users

Every transitive importer from tools/downstream.py is listed, together with the new callers. The original helpers had no external users while private.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | B2 | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | E4 (new) | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixPointwiseRank | E4 | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Imports and uses shared API; theorem signature unchanged |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | API exposed/generalized as above |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No statement or definition changes; no adaptation |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No statement or definition changes; no adaptation |
| TargetsCheck | unclaimed | No statement or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No statement or definition changes; no adaptation |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No statement or definition changes; no adaptation |

## Status

landed 20261016T093726-L-2050747 2026-10-16 (merge of deliver/E4/Sheaf.Paper.IntegralMatrixPointwiseRank)
