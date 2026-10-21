# derived_nakayama_first_reduction proof scopes

## Reason

The completed proof needs the ZeroObject and CategoryTheory.Obj scopes for zero
objects and transported ring-object instances. The file also sets the same proof
elaboration options used by its dependencies. The static interface checker
classifies new file commands conservatively and requires this record. They do
not alter any declaration signature, public import, definition or exported
notation/instance. In particular no target statement or definition is changed.
The private scalar-extensionality helper is fully proved and occurs only in a
public theorem proof.

## Old

The unchanged original command was:

```lean
set_option autoImplicit false
```

There was no added `open scoped` command after the original opens.

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
```

After the original opens:

```lean
open scoped ZeroObject CategoryTheory.Obj
```

The original theorem signature and both public imports stay verbatim. These
scope and elaboration commands affect elaboration of this file; they add no
public declarations or instances to importers.

## Users

The source scan `tools/downstream.py Sheaf.Paper.DerivedNakayamaFirstReduction
--uses derived_nakayama_first_reduction` lists 129 transitive consumers and no
consumer mentioning the theorem yet (only its own declaration). Their existing
statements and definitions do not change: public import visibility is identical,
and local scope opening does not open the scopes in a consuming module. No
consumer is adapted. Current claim holders at the scan are recorded below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.CommonStagePullbackIdentity | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | S1 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | X7 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ConstantWeilStructure | F2 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | X8 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ConstructibleRationalHomComparison | T2 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | X9 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | F4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | W4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.DerivedNakayama | J7 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | A2 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | A3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | Y5 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | G1 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FdCoefficientComparisonSystem | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | Y6 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | A4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | Y8 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | G2 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FiniteProperProductTranspose | N4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | B3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | K5 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralCompositionCounitImages | J3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | T3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | T9 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | G3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | B4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | G4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IsomorphismScalarAugmentationCone | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | Z5 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | H1 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | U4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.PointExactDerivedModel | H2 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.PointTransformationCoefficientDescent | C1 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | H3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | P5 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.PurityFiniteOpenIntervalDescent | H4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.QuotientExpressionKFlatNormalization | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.QuotientSystemMixedCoherence | C2 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.RationalModuleRealizationFunctor | C3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.RationalRealizationPullbackComparison | C4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | F2 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | G2 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | Q6 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | K1 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | H1 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.StrictQuotientExpressions | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | D3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | Z7 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | J1 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | Z9 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | K3 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | A7 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | S4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | R6 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | unclaimed | Same public statements, definitions and imports; no adaptation. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | K4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | D4 | Same public statements, definitions and imports; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Same public statements, definitions and imports; no adaptation. |

## Status

landed 20261021T151153-L-1165057 2026-10-21 (merge of deliver/R4/Sheaf.Paper.DerivedNakayamaFirstReduction)
