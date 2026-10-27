# WeilConjectures.IntegralAmbient canonical functor interfaces

## Reason

The inferred functor interfaces expanded the completed ring, chosen scalar-extension and
monoidal constructions repeatedly during type comparison. Explicit canonical source and target
categories keep these presentations shared. For `push`, the coefficient arguments now name the
same ring sheaf as `integralTowerModules`: the completed commutative ring sheaf with
commutativity forgotten. These are definitionally equal to the original arguments. All other
bodies are unchanged; only the displayed type is supplied. No hypothesis, operation or target
meaning changes. The completed coefficient theorem also has a shorter proof via its existing
adjunction coherence theorem; its statement is unchanged.

## Old

```lean
def push {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
    (S := completedIntegralCoefficientSheafUnrestricted l E Y)
    (R := completedIntegralCoefficientSheafUnrestricted l E X)
    ⟨Functor.whiskerRight (coefficientMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
```

```lean
abbrev pullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (pull l E f).mapHomologicalComplex (.up ℤ)
```

```lean
def pullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  pullComplex l E f ⋙ IntegralOnSlice.tower l E X none
```

```lean
def tensorTower (W : Scheme.{t}) :=
  coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) ⋙ IntegralOnSlice.tower l E W none
```

```lean
def tensorRepresentative (W : Scheme.{t})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :=
  CoefficientTensorModels.iso (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (IntegralOnSlice.duality l E W none).closed
    (IntegralOnSlice.duality l E W none).models P.obj Q.obj P.property.1 Q.property.1
```

## New

```lean
def push {X Y : Scheme.{t}} (f : X ⟶ Y) :
    integralTowerModules l E X ⥤ integralTowerModules l E Y :=
  SheafOfModules.pushforward.{max u (t + 1)} (F := Scheme.proEtaleBaseChange f)
    (J := Scheme.ProEt.topology Y) (K := Scheme.ProEt.topology X)
    (S := SheafOfModules.derivedChangeRingIndependentCoefficients (ProEt.topology Y)
      (completedIntegralCommRingSheafUnrestricted l E Y))
    (R := SheafOfModules.derivedChangeRingIndependentCoefficients (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted l E X))
    ⟨Functor.whiskerRight (coefficientMap l E f).hom
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})⟩
```

```lean
abbrev pullComplex {X Y : Scheme.{t}} (f : X ⟶ Y) :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      CochainComplex (integralTowerModules l E X) ℤ :=
  (pull l E f).mapHomologicalComplex (.up ℤ)
```

```lean
def pullTower {X Y : Scheme.{t}} (f : X ⟶ Y) :
    CochainComplex (integralTowerModules l E Y) ℤ ⥤
      (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E X) ℤ) :=
  pullComplex l E f ⋙ IntegralOnSlice.tower l E X none
```

```lean
def tensorTower (W : Scheme.{t}) :
    (CochainComplex (integralTowerModules l E W) ℤ ×
      CochainComplex (integralTowerModules l E W) ℤ) ⥤
        (ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E W) ℤ) :=
  coefficientTotalTensor.{u, t + 1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W) ⋙ IntegralOnSlice.tower l E W none
```

```lean
def tensorRepresentative (W : Scheme.{t})
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory) :
    DerivedCategory.Q.obj
      ((coefficientTotalTensor.{u, t + 1, t} (ProEt.topology W)
        (completedIntegralCommRingSheafUnrestricted l E W)).obj (P.obj, Q.obj)) ≅
      (IntegralOnSlice.duality l E W none).closed.tensor.obj
        (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) :=
  CoefficientTensorModels.iso (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)
    (IntegralOnSlice.duality l E W none).closed
    (IntegralOnSlice.duality l E W none).models P.obj Q.obj P.property.1 Q.property.1
```

## Users

The current downstream scan has 691 transitive consumers. The following table includes every
textual user reported by `tools/downstream.py --uses` for all five declarations, completed by the
reviewer with the users computed for the review packet (the name
`push` deliberately over-approximates). Their meanings and definitional interfaces are preserved.
No consumer module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.BoundedSiteExchangeTransposes | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.ClosedCoefficientTransposeCocycles | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.ExchangeFunctoriality | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FiniteProjectionExchangeTransposes | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.IntegralAmbientOperationModels | G2 | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.NativeConstantSupportModel | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.PurStrictIntegralExchangeNormalization | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.SfBcCompletedMateDomain | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.SystemClopenMateIdentification | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.SystemEnrichedProjectionAdjunction | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.SystemInternalHomRepresentability | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.SystemTensorPresentationIdentification | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.AmbientExactClopenComparison | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionRecursion | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.OpenClosedWeilMateStructures | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.OpenInterchangeReductionSquares | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.RealizationAdjunctionInsertionShift | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.StrictCompactificationProjectionShift | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.SystemAdjunctionOpenMapShift | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.TensorAdjunctionReductionSquares | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.TriangleProjectionNormalForm | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FiniteFreeComparisonIsomorphismNaturality | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.RamifiedReductionComparisonSquare | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.RationalP1UnitCounit | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed | Definitionally identical operation and category; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Definitionally identical operation and category; no adaptation. |

## Status

landed 20261024T210831-L-42281 2026-10-24 (merge of deliver/G2/Sheaf.Paper.IntegralAmbientOperationModels)
