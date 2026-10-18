# proEtaleRingRestrictionPullbackApp

## Reason

The static preflight classifies added `include` and `attribute` commands as a possible
visibility change and requires this record. The actual change is local proof control:
private coefficient-square helpers use `include comm in`, and local irreducibility
attributes stop elaboration from expanding the tensor-sheafification pullback and the
canonical module adjunction. All existing public signatures and definition bodies are
identical. Explicit intermediate object arguments in the adjunction calculation avoid
trying to infer objects backwards through direct image. The complete module compiled
cleanly in 47.6 seconds with the original 60-second limit.

This does not change a target or any definition it uses. No downstream adaptation is
needed. No other module is edited or claimed. The downstream table records the full
transitive importer list; holders of unedited modules were not queried.

## Old

The existing public definition, verbatim:

```lean
noncomputable def proEtaleRingRestrictionPullbackApp (M : proEtaleRingModules V SV) :
    (proEtaleRingModulePullback f RV RU cR).obj ((proEtaleRingRestrictScalars aV).obj M) ⟶
      (proEtaleRingRestrictScalars aU).obj ((proEtaleRingModulePullback f SV SU cS).obj M) :=
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app M)) ≫
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app
      ((proEtaleRingModulePullback f SV SU cS).obj M)) ≫
  (proEtaleRingModuleAdjunction f RV RU cR).counit.app _
```

There were no local irreducibility attributes for these declarations and no
coefficient-square `include comm in` commands on the new private helpers.

## New

The public definition remains verbatim identical:

```lean
noncomputable def proEtaleRingRestrictionPullbackApp (M : proEtaleRingModules V SV) :
    (proEtaleRingModulePullback f RV RU cR).obj ((proEtaleRingRestrictScalars aV).obj M) ⟶
      (proEtaleRingRestrictScalars aU).obj ((proEtaleRingModulePullback f SV SU cS).obj M) :=
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app M)) ≫
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app
      ((proEtaleRingModulePullback f SV SU cS).obj M)) ≫
  (proEtaleRingModuleAdjunction f RV RU cR).counit.app _
```

The added proof-local reduction command is:

```lean
attribute [local irreducible] proEtaleRingRestrictionPullbackApp
  proEtaleRingModulePullback proEtaleRingModuleAdjunction
```

The added private coefficient-square helpers are each preceded by `include comm in`.
These commands do not export an attribute, notation, instance, variable, or definition.
The original public local-instance commands are retained unchanged. The original
namespace, universe, open commands, and public section-variable block are unchanged;
proved private categorical helpers precede that namespace.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction` | A4 | Proofs and local proof commands only; public signatures and definitions unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.CategoryTheory.ThreeStepAdjunctionComparison` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.BoundedExchangeAmbient` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CoefficientDerivedFunctorAPI` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedClosedCostalkDerivedContinuity` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedConstructibleExtensionTower` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedConstructibleOneStep` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedConstructibleOpenClosedImages` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedFiniteCoefficientLocalization` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedFiniteFamilyHomDescent` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedFiniteLocalSubmodules` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedFiniteModelExtensions` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedFiniteModelProofAPI` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedLfpCoefficientModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedLfpHomContinuity` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedLocalModelGluing` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedLocalPieceCostalkModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedLocallyClosedExtensionTower` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedLocallyClosedOneStep` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarCoefficientConstruction` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarComparisons` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarExchangeLeftAdjunct` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarExchangeRightAdjunct` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarFieldCoefficientSquare` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarFieldEvaluationLinearity` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarFieldFiberExtension` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarFieldPointCoefficientValue` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarFunctionCoefficients` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarFunctionPresentations` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarLfpMatrixRefinement` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarPullbackCube` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedQbarScalarPullback` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedStratumModelInductionStepEmpty` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousAffineEtaleLattice` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousChartSchemeNaturality` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousCoefficientModuleEncoding` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousCoefficientRealizations` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousConstructibleIntegralDenominators` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousConstructibleIntegralGluing` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousConstructibleIntegralTransport` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousEtaleLocalLattices` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousFiniteFreeDenominators` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousFiniteFreeKernelModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralComparisons` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralComplexTelescope` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralExchangeEquality` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralLocalization` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralLocalizationContinuity` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralLocalizationCounit` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralLocalizationHomology` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralLocalizationLegs` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralLocalizationMate` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralLocalizationModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralModuleTelescope` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralPullComposition` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralPushComparison` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralRegularTelescope` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousIntegralUnderivedPushComparison` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLatticeFiniteCoproduct` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLatticeIntersectionLocalModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalization` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitData` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitModel` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLisseCoefficientDescent` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLissePullbackSystem` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLisseStratifiedLattices` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLisseStratumDescent` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousLocallyFreePullback` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousModuleEncodingLattices` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousModuleEncodingLocalFreeness` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousModuleEncodingRestriction` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousModuleEncodingScalarExtension` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousModuleEncodingSliceFreeness` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.ContinuousRegularFunctions` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientEncoding` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientExchange` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientRestriction` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteConstructibleEncoding` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteDerivedCoefficientData` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteEncodedPresentation` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteExchangeComparison` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteExchangeRealization` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteRealizationFunctor` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteDiscreteRestrictionEncoding` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.FiniteEtaleLocallyFreeModels` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralConstructibleKernels` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralConstructibleNakayama` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralConstructibleSerre` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralConstructibleSheafHom` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralExchangeReduction` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralFiniteFreeContractive` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralLfpEventualFreeImage` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralLfpFiniteQuotientCharts` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralLfpHomContinuity` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralLfpLocalTorsionCharts` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralLfpLocallyFreeResolution` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixAnalyticCover` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixAnalyticData` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixCoefficientTransport` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixEntryProperties` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixFunctionsPullback` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixKernelLocallyFree` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixPivotCover` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixPointwiseRank` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralMatrixZeroNeighborhood` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralReductionConservative` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralReductionConstructible` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralRegularCoefficientPullback` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralRegularRationalUnit` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralResidueExchange` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralResidueExchangeAlgebra` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.Paper.IntegralScalarContractive` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.PoincareDuality.CompatibleIntegralRootBases` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.PoincareDuality.CompatiblePrimitiveRoots` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.PoincareDuality.IntegralResidueLimit` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.PoincareDuality.IntegralResidueQuotient` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.PoincareDuality.IntegralTateBasis` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.PoincareDuality.IntegralTateLocalLine` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.PoincareDuality.TateTwistOneLocalLine` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `Sheaf.SmoothPurity.NormalizedWitness` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `TargetsCheck` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.PoincareDuality.Poincare` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.PoincareDuality.Verdier` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.SmoothPurity.Defs` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Basic` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Slop.Basic` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Slop.Main` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.TraceFormula.Statement` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.WeilObject.BoundedConstructible.Defs` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.WeilObject.BoundedConstructible.TensorHom` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |
| `WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar` | Not queried: no edit | No effect: the attributes and include commands are local to the item module. |

## Status

landed 20261018T091357-L-3252935 2026-10-18 (merge of deliver/A4/Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction)
