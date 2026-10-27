# Completed pullback coherent realization extraction

## Reason

The combined item compiled in 78–85 seconds, above the 60-second limit.
A separate rebuild of the unchanged original item also takes 70 seconds. Profiling
showed the new derived-comparison proof was small after abstract factoring, while
the existing declaration block still dominated total checking and serialization.
The extracted block now compiles separately. This relocates 71 existing public
declarations, with identical signatures, bodies and attributes; it introduces no
mathematical definition or statement change. The 11 holes in that block retain
their original names and statements. The complete declaration list is in
`dag/nodes/sec-smooth-purity/def-pur-completed-pullback-tower-realizations.json`.

## Old

The coherent reduction and strict tower declarations, including this representative definition,
were defined in `Sheaf.Paper.CompletedPullbackTensorComparison`:

```lean
def pullbackTensorLimitRoos (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (integralOperationsRoos (pullbackTensorRestrictedTower l E W C)) :=
  (coefficientConstantTowerLimit l E W).mapIso
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app C) ≪≫
  (pullbackTensorRoosModel l E W).app
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)
```

The original module marked `pullbackTensorUniqueChoice` reducible at its end.

## New

The same declaration block is defined in
`Sheaf.Paper.CompletedPullbackTowerRealizations` and publicly re-exported by the
original item module. This definition is unchanged:

```lean
def pullbackTensorLimitRoos (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj C) ≅
      DerivedCategory.Q.obj (integralOperationsRoos (pullbackTensorRestrictedTower l E W C)) :=
  (coefficientConstantTowerLimit l E W).mapIso
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app C) ≪≫
  (pullbackTensorRoosModel l E W).app
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)
```

The reducible attribute is applied in the new defining module, as Lean requires.
The original module retains a proved private `pullbackTensorSequenceRing_eq` with
its old signature and body for existing import-all consumers. All original public
imports remain in the item. The extracted module uses only the construction and
proof imports needed by its block. The item removes seven private proof imports
used only by that block; the extracted module retains them. Their complete list
is in the report under No longer needed.

Reviewer addition: the item node `def-pur-completed-pullback-tensor-comparison`
gains `def-pur-completed-pullback-tower-realizations` in `stmt_deps`, because the
item's own statements and definitions (`pullbackTensorComparisonCounits`,
`canonicalIntegralPullbackTensor`) are stated with declarations now owned by that
node (`pullbackTensorCalculus`, `pullbackTensorSequenceDerived`,
`pullbackTensorIntegralPullbackModel`, `pullbackTensorReferenceTensor`). The node's
statement text is unchanged.

## Users

The item and its direct importers below are compiled against the packet. No
consumer source adaptation is part of this delivery. The two import-all consumers
that use the retained private lemma are ProperSupportStepBounds and
ScalarExtensionTowerCoherence.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.SixFunctors.BasicRealizationShiftSquare` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.SixFunctors.IntegralSystemOperations` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.SixFunctors.ProperSupportStepBounds` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.SixFunctors.SystemPullbackCompositorIdentification` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.DerivedPullbackTensorIso` | J4 | Times out both with the packet and on the original library; no adaptation. |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.PodCompletionReindexModels` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.SixFunctorOperationDatumStages` | unclaimed | 68 seconds against the packet, 66 seconds on the original baseline; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPuritySystems` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.DerivedAutomorphismHomEvaluation` | unclaimed | 83–118 seconds against the packet; 86 seconds against a fresh original-item artifact; no adaptation. |
| `Sheaf.Paper.CommonStageWeilLinearDual` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.CompletedComparisonQuotientRealizationDefs` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.PointWeilPairingCoordinates` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.RegularCoefficientCoherentReduction` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Passes unchanged against the packet. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed | 68 seconds against the packet, 77 seconds against a rebuilt original item; no adaptation. |
| `Sheaf.Paper.TwistedPullbackReductionData` | unclaimed | Passes unchanged against the packet in 48.7 seconds. |


The unchanged `DerivedPullbackTensorIso` also exceeded the 120-second diagnostic
stop when compiled in an isolated scratch root with no sandbox artifacts. That
baseline used the same source, with only the profiler enabled. Thus this is an
existing timeout, not a failure introduced by the extraction. The source SHA256
was `6601ee9d1ab3eb4f187006c57b7ee4aa2e95645879ecfdb80347585db3a51945`. This held module is not adapted or delivered.

The unchanged `SixFunctorOperationDatumStages` took 68 seconds against the packet
and 66 seconds in the same isolated baseline setup. This also exceeds the limit
before the extraction and is not adapted or delivered.

The unchanged `DerivedAutomorphismHomEvaluation` initially passed in 49.5 seconds
against the published library, but that library was not the current restored item
source. Rebuilding the unchanged original item in an isolated scratch root takes
70 seconds and writes its compiled artifact. The unchanged consumer then takes
86 seconds against that artifact, compared with 83–118 seconds against the packet.
It therefore also has a pre-existing source-level timeout. No consumer adaptation
is delivered; exploratory edits were discarded.


Additional textual users of all 71 extracted declarations (the downstream tool
searches whole names after stripping comments). The interfaces and meanings of
these indirect uses are unchanged; no adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AdicPurityExceptionalReduction` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.AdicPurityObjects` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.CanonicalTateArrowNaturality` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.CommonStageTensorLineCoherenceNaturality` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.CommonStageTensorRightUnitorNaturality` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.CompletedComparisonQuotientNormalization` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.CompletedComparisonQuotientRealization` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | claimed | Own item; same declarations are re-exported from the extracted module. |
| `Sheaf.Paper.CompletedTensorHomTranspose` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.FiniteExceptionalSiteNormalization` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.GeometricFrobeniusInternalHomComparison` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.NormalizedOrientationPerfectDuality` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.NormalizedRationalEvaluationNaturality` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.PodCompletionReindexSubstitution` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.PodReindexingCompletedEvaluationReflection` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.RationalTwistedPullbackCompositor` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.ReindexingSystemHomReductionSquare` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.SystemClopenMateIdentification` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.SystemProjectionTriangleCompatibility` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.SystemTensorPresentationData` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.Paper.SystemTensorPresentationIdentification` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.AmbientProperOpenCalculus` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.BasicSystemShiftResolutionCalculus` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeData` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.FiniteAdjunctionSystemData` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.GeneratorReductionData` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralBasicRealization` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralBasicRealizationData` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralCompactificationRealizationData` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralExpressionRecursion` | claimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralRealizationAssemblyData` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.IntegralSystemCompositorAssociativity` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.OpenReconstructionEffectivity` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.OpenReductionMateLocalization` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.OrdinaryOpenReductionMate` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.PrimitiveQuotientAugmentations` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.PullQuotientAugmentationOnGood` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.RefinementProjectionProperComposition` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.SystemProperOpenProjectionShift` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.SystemTensorLeftShiftUnique` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.SystemTensorRightShiftUnique` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.TensorAdjunctionReductionSquares` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |
| `Sheaf.SixFunctors.TensorQuotientAugmentationOnGood` | unclaimed | Indirect user; signatures, bodies and attributes preserved by public re-export. |

The two additional restored direct consumers were also checked. The unchanged
`RelativeProductBaseChangeFactorSquares` takes 68 seconds against this packet and
77 seconds against the freshly rebuilt original item. It is not adapted.
`TwistedPullbackReductionData` passes unchanged in 48.7 seconds. Both consumer
copies were removed, leaving only the three intended Lean delivery files.

## Status

landed 20261026T235951-L-1474437 2026-10-26 (merge of deliver/V4/Sheaf.Paper.CompletedPullbackTensorComparison)
