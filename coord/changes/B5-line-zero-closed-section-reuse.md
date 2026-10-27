# Closed-section comparison construction reuse

## Reason

The original item spends most of its per-file compile limit rechecking the expanded
proper/exact comparison constructions. The new generic comparison modules
contains those same explicit constructions with named endpoints. Reuse them in the
item so subsequent references are checked against a compact named expression.
The source isomorphisms are definitionally equal to the original formulas: no map,
normalization, hypothesis, or public signature changes. The new module is a public
import because these definition bodies refer to its public constructions.

## Old

```lean
def lineZeroEtaleTarget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  ⟨((DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.frameTwistEtale T 1))⟦(2 : ℤ)⟧,
    DerivedCategory.TStructure.t.plus.le_shift (2 : ℤ) _
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.frameTwistEtale T 1)).property⟩
```

```lean
def lineZeroProTarget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  ⟨((DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.functorialCupTwist true T 1))⟦(2 : ℤ)⟧,
    DerivedCategory.TStructure.t.plus.le_shift (2 : ℤ) _
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) 0).obj
        (P.functorialCupTwist true T 1)).property⟩
```

```lean
def lineZeroTwistComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (P.lineZeroEtaleTarget T).obj ≅ (P.lineZeroProTarget T).obj :=
  ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.commShiftIso
    (2 : ℤ)).app
    ((DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) 0).obj
      (P.frameTwistEtale T 1)) ≪≫
  (shiftFunctor _ (2 : ℤ)).mapIso
    (((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategorySingleFunctor
      0).app
      (P.frameTwistEtale T 1))
```

```lean
def lineZeroEtaleMap (V : PurityVectorBundle P B b 1) :
    lineZeroEtaleSource V ⟶ P.lineZeroEtaleTarget V.E :=
  ObjectProperty.homMk (lineZeroExtHom
    (P.agreementCartierEtale (V.p ≫ b) V.zeroSection (lineZeroIdeal V)))
```

```lean
def lineZeroProMap (V : PurityVectorBundle P B b 1) :
    lineZeroProSource V ⟶ P.lineZeroProTarget V.E :=
  ObjectProperty.homMk (P.agreementCartierMap (V.p ≫ b) V.zeroSection (lineZeroIdeal V))
```

```lean
def lineZeroUnitComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (P.lineZeroEtaleUnit T).obj ≅ (P.lineZeroProUnit T).obj :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategorySingleFunctor 0 |>.app
    (P.constantEtale T)
```

```lean
def lineZeroSupportedComparison (V : PurityVectorBundle P B b 1) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V.E).mapDerivedCategory.obj
      (lineZeroEtaleSource V).obj ≅ (lineZeroProSource V).obj :=
  ((comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V.E).mapDerivedCategorySingleFunctor
    0).app
    (P.functorialCupSource false V.zeroSection) ≪≫
  (DerivedCategory.singleFunctor
      (Sheaf (Scheme.ProEt.topology V.E) (ModuleCat.{u + 1} P.Coefficient)) 0).mapIso
    (P.functorialCupComparisonSource_existsUnique V.zeroSection).choose
```

```lean
def lineZeroProClosedIso (V : PurityVectorBundle P B b 1) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).obj (P.lineZeroOriginUnit B).obj ≅ (lineZeroProSource V).obj :=
  (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
    V.zeroSection).mapIso (P.lineZeroUnitComparison B) ≪≫
  (ProEtale.rightDerivedLowerShriekIsoOfIsProper
    (ModuleCat.{u + 1} P.Coefficient) V.zeroSection).app _ ≪≫
  (ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
    V.zeroSection).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
  ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
    V.zeroSection).mapDerivedCategorySingleFunctor 0).app (P.constant B)
```

```lean
def lineZeroEtaleClosedIso (V : PurityVectorBundle P B b 1) :
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).obj (P.lineZeroEtaleUnit B) ≅ lineZeroEtaleSource V :=
  DerivedCategory.Plus.ι.preimageIso
    ((Etale.rightDerivedLowerShriekPlusCompatibility
      (ModuleCat.{u + 1} P.Coefficient) V.zeroSection).app _ ≪≫
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
      (ModuleCat.{u + 1} P.Coefficient) V.zeroSection).app _ ≪≫
    (Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).rightDerivedFunctorIsoMapDerivedCategory.app _ ≪≫
    ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).mapDerivedCategorySingleFunctor 0).app (P.constantEtale B))
```

```lean
def lineZeroProSourceIso (V : PurityVectorBundle P B b 1) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
      (lineZeroProSource V).obj ≅ (P.lineZeroProUnit B).obj :=
  (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).mapIso
    (lineZeroProClosedIso V).symm ≪≫
  (ProEtale.originCompositionAmbient P.Coefficient V.zeroSection V.p).app
    (P.lineZeroOriginUnit B) ≪≫
  (ProEtale.rightDerivedLowerShriekCongr (ModuleCat.{u + 1} P.Coefficient)
    V.zeroSection_spec.1).app _ ≪≫
  (ProEtale.DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} P.Coefficient) B).ι.mapIso
    ((ProEtale.originCompactSupportId P.Coefficient B).app (P.lineZeroOriginUnit B)) ≪≫
  P.lineZeroUnitComparison B
```

```lean
def lineZeroEtaleSourceIso (V : PurityVectorBundle P B b 1) :
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).obj
      (lineZeroEtaleSource V) ≅ P.lineZeroEtaleUnit B :=
  (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).mapIso
    (lineZeroEtaleClosedIso V).symm ≪≫
  (Etale.rightDerivedLowerShriekPlusCompIso P.Coefficient V.zeroSection V.p).app
    (P.lineZeroEtaleUnit B) ≪≫
  (Etale.rightDerivedLowerShriekPlusCongr P.Coefficient V.zeroSection_spec.1).app _ ≪≫
  (Etale.rightDerivedLowerShriekPlusId P.Coefficient B).app _
```

```lean
def lineZeroCompactSourceComparison (V : PurityVectorBundle P B b 1) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (lineZeroEtaleSource V)).obj ≅
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (lineZeroProSource V).obj :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.mapIso
    ((Etale.rightDerivedLowerShriekPlusCompatibility
      (ModuleCat.{u + 1} P.Coefficient) V.p).app (lineZeroEtaleSource V)) ≪≫
  ((compactSupportSiteComparison P.Coefficient
    (HasCompactification.compactification V.p)).app (lineZeroEtaleSource V)).symm ≪≫
  (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).mapIso
    (lineZeroSupportedComparison V)
```

## New

```lean
def lineZeroEtaleTarget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)) :=
  P.cartierComparisonEtaleTarget T
```

```lean
def lineZeroProTarget (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} P.Coefficient)) :=
  P.cartierComparisonProTarget T
```

```lean
def lineZeroTwistComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (P.lineZeroEtaleTarget T).obj ≅ (P.lineZeroProTarget T).obj :=
  P.cartierComparisonTwist T
```

```lean
def lineZeroEtaleMap (V : PurityVectorBundle P B b 1) :
    lineZeroEtaleSource V ⟶ P.lineZeroEtaleTarget V.E :=
  P.cartierComparisonEtaleMap (V.p ≫ b) V.zeroSection (lineZeroIdeal V)
```

```lean
def lineZeroProMap (V : PurityVectorBundle P B b 1) :
    lineZeroProSource V ⟶ P.lineZeroProTarget V.E :=
  P.cartierComparisonProMap (V.p ≫ b) V.zeroSection (lineZeroIdeal V)
```

```lean
def lineZeroUnitComparison (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
      (P.lineZeroEtaleUnit T).obj ≅ (P.lineZeroProUnit T).obj :=
  closedSectionChi P T
```

```lean
def lineZeroSupportedComparison (V : PurityVectorBundle P B b 1) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) V.E).mapDerivedCategory.obj
      (lineZeroEtaleSource V).obj ≅ (lineZeroProSource V).obj :=
  closedSectionEpsilon P V.zeroSection
```

```lean
def lineZeroProClosedIso (V : PurityVectorBundle P B b 1) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).obj (P.lineZeroOriginUnit B).obj ≅ (lineZeroProSource V).obj :=
  closedSectionIp P V.zeroSection
```

```lean
def lineZeroEtaleClosedIso (V : PurityVectorBundle P B b 1) :
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient)
      V.zeroSection).obj (P.lineZeroEtaleUnit B) ≅ lineZeroEtaleSource V :=
  closedSectionIe P V.zeroSection
```

```lean
def lineZeroProSourceIso (V : PurityVectorBundle P B b 1) :
    (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
      (lineZeroProSource V).obj ≅ (P.lineZeroProUnit B).obj :=
  closedSectionSigmap P V.p V.zeroSection V.zeroSection_spec.1
```

```lean
def lineZeroEtaleSourceIso (V : PurityVectorBundle P B b 1) :
    (Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).obj
      (lineZeroEtaleSource V) ≅ P.lineZeroEtaleUnit B :=
  closedSectionSigmae P V.p V.zeroSection V.zeroSection_spec.1
```

```lean
def lineZeroCompactSourceComparison (V : PurityVectorBundle P B b 1) :
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) B).mapDerivedCategory.obj
      ((Etale.rightDerivedLowerShriekPlus (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (lineZeroEtaleSource V)).obj ≅
      (ProEtale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) V.p).obj
        (lineZeroProSource V).obj :=
  closedSectionBeta P V.p V.zeroSection
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.LineZeroClassEtaleRealization | B5 | Definitionally equal construction reuse; proof completed from the split source normalization. |

The downstream textual usage audit is recorded in the report. Every unchanged
consumer sees the same definitions after unfolding. No consumer adaptation is forced.
No statement in Challenge.lean changes meaning, since each replaced definition
expands to its previous term.

## Status

landed 20261025T201419-L-2491978 2026-10-25 (merge of deliver/B5/Sheaf.Paper.LineZeroClassEtaleRealization)
