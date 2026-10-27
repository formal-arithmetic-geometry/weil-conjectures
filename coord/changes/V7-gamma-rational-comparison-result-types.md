# Explicit result types for coefficient Gamma constructions

## Reason

Remote compilation repeatedly exceeded 60 seconds after adding the inverse-law
proof. Profiling showed the rational endpoint constructions spending several
seconds inferring and checking expanded result types. Give seven existing
constructions their already inferred arrow/functor/equivalence types explicitly.
Every parameter and body is unchanged. Local irreducibility settings keep large
Hom-chain constructions folded, and both respectTransparency options are true;
no exported reducibility attribute changes. The canonical `Algebra.toModule`
instance gets priority 2000 locally to avoid irrelevant instance search;
this changes no exported instance priority.

## Old

```lean
def rationalization (W : SixFunctorSpace D) :=
  (PodCoefficientStage.domain S .integral W).ι ⋙
    sfRationalConstructibleLocalization C.l E W.obj.left
```

```lean
def rationalGammaIso
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory) :=
  (rationalization S Y).mapIso (integralGammaIso S f c R M N)
```

```lean
def rationalGamma
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory)
    (L : sfRationalConstructibleCategory C.l E Y.obj.left) :=
  Iso.homCongr (Iso.refl L) (rationalGammaIso S f c R M N)
```

```lean
def commonGamma (L : Pair C.l C.Qbar Y.obj.left) :=
  Iso.homCongr (Iso.refl L) (commonGammaIso F SF f c RF M N)
```

```lean
def shiftedIntegralGamma (r : ℤ) :=
  (shiftFunctor (sfIntegralConstructibleCategory C.l
    (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).map
      (integralGammaIso SF f c RF M N).hom.hom
```

```lean
def rationalSourceComparison
    (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) :=
  rY.inv.app ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N) ≫
    (rationalization SG Y).map (d.source M N)
```

```lean
def rationalTargetComparison
    (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) :=
  rY.inv.app ((PodHomChain.targetFunctor SF .integral f c RF M).obj N) ≫
    (rationalization SG Y).map (d.target M N)
```

## New

```lean
def rationalization (W : SixFunctorSpace D) :
    (PodCoefficientStage.domain S .integral W).FullSubcategory ⥤
      sfRationalConstructibleCategory C.l E W.obj.left :=
  (PodCoefficientStage.domain S .integral W).ι ⋙
    sfRationalConstructibleLocalization C.l E W.obj.left
```

```lean
def rationalGammaIso
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory) :
    (rationalization S Y).obj ((PodHomChain.sourceFunctor S .integral f c R M).obj N) ≅
      (rationalization S Y).obj ((PodHomChain.targetFunctor S .integral f c R M).obj N) :=
  (rationalization S Y).mapIso (integralGammaIso S f c R M N)
```

```lean
def rationalGamma
    (M : (PodCoefficientStage.domain S .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain S .integral Y).FullSubcategory)
    (L : sfRationalConstructibleCategory C.l E Y.obj.left) :
    (L ⟶ (rationalization S Y).obj ((PodHomChain.sourceFunctor S .integral f c R M).obj N)) ≃
      (L ⟶ (rationalization S Y).obj ((PodHomChain.targetFunctor S .integral f c R M).obj N)) :=
  Iso.homCongr (Iso.refl L) (rationalGammaIso S f c R M N)
```

```lean
def commonGamma (L : Pair C.l C.Qbar Y.obj.left) :
    (L ⟶ commonSource F SF f c RF M N) ≃ (L ⟶ commonTarget F SF f c RF M N) :=
  Iso.homCongr (Iso.refl L) (commonGammaIso F SF f c RF M N)
```

```lean
def shiftedIntegralGamma (r : ℤ) :
    (shiftFunctor (sfIntegralConstructibleCategory C.l
      (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).obj
        ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N).obj ⟶
    (shiftFunctor (sfIntegralConstructibleCategory C.l
      (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).obj
        ((PodHomChain.targetFunctor SF .integral f c RF M).obj N).obj :=
  (shiftFunctor (sfIntegralConstructibleCategory C.l
    (Coefficient.{u} C.l C.Qbar F) Y.obj.left) r).map
      (integralGammaIso SF f c RF M N).hom.hom
```

```lean
def rationalSourceComparison
    (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) :
    (stageTransition C.l C.Qbar Y.obj.left F G hFG).obj
      ((rationalization SF Y).obj ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N)) ⟶
    (rationalization SG Y).obj
      ((PodHomChain.sourceFunctor SG .integral f c RG (TX.obj M)).obj (TY.obj N)) :=
  rY.inv.app ((PodHomChain.sourceFunctor SF .integral f c RF M).obj N) ≫
    (rationalization SG Y).map (d.source M N)
```

```lean
def rationalTargetComparison
    (M : (PodCoefficientStage.domain SF .integral X).FullSubcategory)
    (N : (PodCoefficientStage.domain SF .integral Y).FullSubcategory) :
    (stageTransition C.l C.Qbar Y.obj.left F G hFG).obj
      ((rationalization SF Y).obj ((PodHomChain.targetFunctor SF .integral f c RF M).obj N)) ⟶
    (rationalization SG Y).obj
      ((PodHomChain.targetFunctor SG .integral f c RG (TX.obj M)).obj (TY.obj N)) :=
  rY.inv.app ((PodHomChain.targetFunctor SF .integral f c RF M).obj N) ≫
    (rationalization SG Y).map (d.target M N)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientGammaRepresentatives | V7 | Explicit result types on existing constructions; same definition bodies and elaborated mathematical interfaces. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed in local claim snapshot | Downstream consumer of the same functors and representatives; no change of arguments, arrow types, or bodies; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | unclaimed in local claim snapshot | Downstream importer retaining the same coefficient-Gamma interface; no adaptation. |

`tools/downstream.py` reports exactly these two downstream modules. The two
`--uses rationalSourceComparison`/`--uses rationalTargetComparison` checks each
report only the defining module. The other annotations explicitly present the
same inferred types, so existing consumers require no proof adaptation. No
statement or definition changes its mathematical meaning, and targets do not
require statement correction.

## Status

landed 20261025T164611-L-1039191 2026-10-25 (merge of deliver/V7/Sheaf.Paper.CoefficientGammaRepresentatives)
