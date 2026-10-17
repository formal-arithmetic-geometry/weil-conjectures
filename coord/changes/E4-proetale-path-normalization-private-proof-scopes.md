# AlgebraicGeometry.ProEtale.comparisonSquareProEtalePath_normalization

## Reason

The preflight conservatively flags added section variables and local attributes as
commands that can affect importers. These commands support four fully proved private
helpers. The generic variables are contained in a section; the only added attribute is
`attribute [local implicit_reducible] upperStar Etale.upperStar comparisonUpperStar`.
Its effect ends at this module's namespace scope. No global instance or simplification
rule is added. The only added import is proof-only. The public theorem keeps exactly
its original signature, visibility, and docstring. Its former `sorry` is proved.

## Old

```lean
theorem comparisonSquareProEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareProEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((leftDerivedUpperStarComparisonIso f' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
            ((leftDerivedUpperStarComparisonIso g Λ).hom.app M) ≫
          (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
            ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M))
```

## New

```lean
theorem comparisonSquareProEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareProEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((leftDerivedUpperStarComparisonIso f' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
            ((leftDerivedUpperStarComparisonIso g Λ).hom.app M) ≫
          (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
            ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M))
```

The signature is identical. Four proved private lemmas implement the existing proof
plan. There are no changed definitions, new public constants, or consumer adaptations.
No target statement or definition used by a target changes meaning.

## Users

`tools/downstream.py` lists the following transitive consumers. Its `--uses` search
finds only the item itself and `ComparisonSquareTransport`; all existing uses remain
valid because the public type and visible imports are unchanged. No module listed
below is modified, so its current claim does not affect this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization | E4 | One theorem proved; public interface unchanged. |
| Sheaf.Paper.FiniteConstantCokernel | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.IntegralExchangeReduction | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.ProEtaleStratifiedCounit | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport | not adapted | Public interface unchanged; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | not adapted | Public interface unchanged; no adaptation needed. |
| TargetsCheck | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.Statement | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.TraceFormula.Slop.Main | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.WeilSheaf.PoincareDuality | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.Examples | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted | Public interface unchanged; no adaptation needed. |
| WeilConjectures.ZetaFunction.Weights | not adapted | Public interface unchanged; no adaptation needed. |

## Status

landed 20261017T003418-L-3314016 2026-10-17 (merge of deliver/E4/Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareProEtalePathNormalization)
