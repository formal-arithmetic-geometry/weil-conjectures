# comparisonSquareEtalePath_normalization

## Reason

The delivery completes the proof of the unchanged theorem. The interface scanner
conservatively flags newly added file-local attributes, options, and the variables in
the closed `ExactPath` section. This record documents those proof-development commands.
They provide the abstract parameters for proved private helpers and prevent elaboration
from unfolding the sheaf pullback and exact derived-functor constructions prematurely.
The attributes are local; the options are file-local; the variables are inside a section
which ends before the concrete helper declarations. No target or public definition changes.

## Old

The original exported statement was:

```lean
theorem comparisonSquareEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
            ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
          (leftDerivedUpperStarComparisonIso g' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
            ((leftDerivedUpperStarComparisonIso f Λ).hom.app M))
```

The only pre-existing local attribute command was:

```lean
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

## New

The exported statement remains verbatim:

```lean
theorem comparisonSquareEtalePath_normalization
    (Λ : Type (u + 1)) [CommRing Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    HEq
      (comparisonSquareDerivedPath Λ g' f' f g (comparisonSquareEtalePath Λ
        { toCommSq := sq.toCommSq, isoPullback := sq.isoPullback,
          hom_fst := sq.isoPullback_hom_fst, hom_snd := sq.isoPullback_hom_snd }) M)
      ((DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
            ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
          (leftDerivedUpperStarComparisonIso g' Λ).hom.app
            (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
          L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
            ((leftDerivedUpperStarComparisonIso f Λ).hom.app M))
```

The added local commands and closed helper-section parameters are:

```lean
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  Functor.mapDerivedCategory Functor.mapDerivedCategoryNatIso

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section ExactPath

variable {A B B' C P Q R : Type*}
  [Category A] [Category B] [Category B'] [Category C]
  [Category P] [Category Q] [Category R]
  [Abelian A] [Abelian B] [Abelian B'] [Abelian C]
  [Abelian P] [Abelian Q] [Abelian R]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory B']
  [HasDerivedCategory C] [HasDerivedCategory P] [HasDerivedCategory Q]
  [HasDerivedCategory R]
  (F : A ⥤ B) (G : B ⥤ C) (F' : A ⥤ B') (G' : B' ⥤ C)
  (K₀ : A ⥤ P) (K₁ : B' ⥤ Q) (K₂ : C ⥤ R) (P₁ : P ⥤ Q) (P₂ : Q ⥤ R)
  [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
  [K₀.Additive] [K₁.Additive] [K₂.Additive] [P₁.Additive] [P₂.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits K₀] [PreservesFiniteColimits K₀]
  [PreservesFiniteLimits K₁] [PreservesFiniteColimits K₁]
  [PreservesFiniteLimits K₂] [PreservesFiniteColimits K₂]
  [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
```

`end ExactPath` closes the section. Every helper added within it is private and proved.
The theorem proof additionally imports `Sheaf.Paper.DerivedSquarePasting` privately.
The module retains its original public import of `ComparisonSquarePaths`.

## Users

`tools/downstream.py` reports 57 downstream modules and two textual mentions of the
assigned declaration (the item itself and `ComparisonSquareTransport`). Every row below
has the same exported statements, definitions, and public imports after the delivery.
No module is adapted. No target-statement review is reopened because no target
statement or definition used by a target changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization | E3 | Original signature; proof completed. |
| Sheaf.Paper.FiniteConstantCokernel | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleStratifiedCounit | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquare | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareTransport | unclaimed | Unchanged interface and meaning; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged interface and meaning; no adaptation. |
| TargetsCheck | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FullCohomologicalDimension | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.WeaklyContractibleCohomology | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.Statement | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Unchanged interface and meaning; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Unchanged interface and meaning; no adaptation. |

## Status

landed 20261017T021601-L-694009 2026-10-17 (merge of deliver/E3/Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonSquareEtalePathNormalization)
