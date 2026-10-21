# Sheaf.Paper.FiniteCoefficientReductionFlatModel proof elaboration

## Reason

Stage-3 preflight requires a change record for the new file-level options, opens and local
attributes. The proofs need the existing monoidal notation/API and independent-universe
instance search. Local irreducibility keeps large localization and tensor constructions
behind their comparison APIs. In the etale section, priority 2000 for `CommRing.toRing`
selects the same definitionally equal ring projection for generic rings and their ULifts.
Without that priority, the kernel repeatedly normalizes the chosen coefficient subring
while comparing the generic model theorem with the finite-stage target, exceeding 60 seconds.
With it, the complete module compiles cleanly in 32.4 seconds.

These are file-local elaboration changes. Existing public imports, declaration statements,
definition bodies and docstrings are unchanged. Ring operations and mathematical objects
are unchanged; the alternative instance paths are definitionally equal. Added helpers are
private proved theorems. No downstream adaptation or target statement change is needed.
The original coefficient-extension proof import is retained explicitly for the unit route.

## Old

```lean
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
```

There were no local irreducibility or instance-priority attributes in the module.

## New

```lean

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] _root_.DerivedCategory.monoidalClosed
  SheafOfModules.monoidalCategory CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.presheafToSheaf CategoryTheory.sheafCompose
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  AlgebraicGeometry.Etale.derivedTensor
  AlgebraicGeometry.Etale.derivedTensorQObjSingleFunctorObjIso

attribute [local irreducible] flatModelReductionData flatModelReductionDerivedData
  Functor.mapHomotopyCategory DerivedCategory.Qh DerivedCategory.Q
  SheafOfModules.changeOfRings SheafOfModules.changeOfRingsHom

attribute [local irreducible] flatModelReductionChange flatModelReduction

attribute [local instance 2000] CommRing.toRing

open CategoryTheory CategoryTheory.Limits MonoidalCategory
```

The attributes are local to this module. The ring-instance priority is introduced after the
pro-etale namespace, before the etale proofs. Original universes and variable declarations
are retained; their source positions move only because proved private helpers are inserted.

## Users

`tools/downstream.py Sheaf.Paper.FiniteCoefficientReductionFlatModel` lists the following
transitive consumers. Their current claim holders are recorded below. None is edited:
local commands do not propagate to importers and every existing public declaration retains
its statement and definitionally equal data. No consumer fails to compile due to an API change.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.A1FiniteWeilSectionsDecomposition` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.A1LisseSectionEvaluation` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.A1LisseSectionsStalkEvaluation` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.AdicCompactificationSectionRealization` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.AdicSectionCanonicalModels` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.AdicSectionClosedSupport` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.AffineCurveHcZero` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.AmbientDiagonalPurityBaseChange` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CommonAdicCompactificationSectionData` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CommonAdicOpenSectionData` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CommonAdicSectionData` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CommonStageCompactWeilCohomology` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CompactSupportPerfectness` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CompactSupportSystemRealizationNormalization` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CompactifiedTowerComparisons` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CompletedStalkReparametrizationCoherence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ConnectedConstantH0` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ConstantExtensionCompactComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ConstantExtensionMixedDescent` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ConstructibleDegreeZeroProperSupport` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.DegreeZeroCompactSupportSections` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.DualStalkFrobenius` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.EtaleLocallyClosedShriek` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ExtensionByZeroPunctual` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteAdicCompactificationSectionData` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteAdicImageNormalization` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteAdicOpenSectionData` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteAdicOrdinarySectionData` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteAdicProperSectionData` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteAdicSectionRealizationCore` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteBoundaryWeights` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientHomChange` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | A4 | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | Y7 | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | Y8 | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteEtaleDescent` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteProperLocalizing` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteStructuralMapsCommShift` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionCoherence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FrobeniusCoefficientReductionMap` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FrobeniusExchangeDegreeZero` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FrobeniusFixesUnitSection` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.GlobalGeometricFrobenius` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ImmersionWeilLocalBehavior` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.IntegralCompactTransportSystemMatePasting` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.IntegralProperBaseChange` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.IntegralProperConstructibleHeartBound` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.InternalHomPullback` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.IteratedWeilCocycle` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.IteratedWeilMap` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusCoefficientExtension` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacy` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusConjugacyClass` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.OpenCompactSupportFiniteTor` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.OpenImmersionLocalizing` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactCohomology` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.OrdinaryCompactWeilCohomology` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PoincarePointFiniteness` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PointCompletedEvaluation` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PointSectionsCompletionCone` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PointSystemPowerRoosCoherence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PointSystemRoosTransport` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PointSystemTransportDescent` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PointTransportConeComparisonDescent` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PointTransportStrictQuotient` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PointWeilHeartFlag` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ProperBaseChangeRational` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ProperCoincidenceFrobenius` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ProperCompactCoincidence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ProperHeartBound` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ProperHeartConstructibleCohomology` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ProperOpenBoundaryZero` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ProperSectionsSemilinearGerms` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.PurityGeneralAdmissibility` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.RealSheavesCohomologyEulerSeries` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SitePerfectCoefficientDual` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SitePerfectDualizableHom` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SmoothPurityQbar` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceCohomologicalCorrespondence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceCompactificationCohomology` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceFixedScheme` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceFormulaAdicSystem` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceFormulaCoefficientConventions` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceFormulaCurveIntegralLattice` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceFormulaLocalFrobeniusOperator` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceFormulaStrictWeilComplex` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TraceGraphCorrespondence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TrfDevissageGeneration` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TrfWitnessedOpenPullback` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TwConventions` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.TwistFrobeniusScalar` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.WeilCohomologyScalarExtensionQlbar` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.WeilConstantExtensionFrobenius` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | U1 | Unchanged API; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransport` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusOpenExchange` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.GraphFrobeniusPointExchange` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.InternalHomPullback` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.SchemeGaloisPullbackNaturality` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.SelectedSchemeGaloisComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | Unchanged API; no adaptation. |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Unchanged API; no adaptation. |
| `WeilConjectures` | unclaimed | Unchanged API; no adaptation. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | Unchanged API; no adaptation. |

## Status

landed 20261021T233811-L-864563 2026-10-21 (merge of deliver/Y6/Sheaf.Paper.FiniteCoefficientReductionFlatModel)
