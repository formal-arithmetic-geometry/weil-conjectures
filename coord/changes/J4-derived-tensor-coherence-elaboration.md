# DerivedPullbackTensorIso local elaboration context

## Reason

Restore the assigned quarantined module with every canonical construction and existing
proof intact. The unchanged archive exceeded the 120-second diagnostic cutoff; its
imports alone compiled in 3.4 seconds. With cached Hom structures the rational
associativity proof finishes in about six seconds. The prefix through rational braiding
compiles in 33.8 seconds. The final common-stage block requires the same cached category
interfaces already used by `DerivedPullbackTensorHom`.

## Old

All declarations, definition data, proof bodies and imports are retained. The archived
file had no local style-scan options, no separate rational-coherence elaboration section,
and no final common-stage category cache block.

## New

Added local options after `autoImplicit`:

```lean
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
```

Inserted a section after the existing integral/rational associator attributes:

```lean
section RationalCoherenceElaboration
attribute [local irreducible] sfIntegralConstructible Linear.homModule Preadditive.homGroup
```

It ends immediately before `reducedBraiding_natural`. This keeps the later abstract
linear induction proof in its original context and avoids duplicating the subsequent
local irreducibility attribute for `sfIntegralConstructible`.

Before `canonicalCommonStagePullbackTensor_braiding_spec`:

```lean
attribute [local irreducible] ObjectProperty.FullSubcategory.category
  ScalarLocalization.category ScalarLocalization.linear
set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
```

The scoped validation override matches the operation module's existing treatment of
its reducible stage-system abbreviation. It changes only local elaborator reducibility.
The final existing assembly barrier also includes `canonicalCommonStagePullbackTensor`.
Every declaration signature, definition body, public import and exported attribute stays
verbatim. No definition used by a target changes its meaning; no target review is reopened.

## Users

Direct importers are listed below. None needs adaptation: the exported interface,
including reducibility attributes visible to importers, is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CommonStageShiftedUnitTensor | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CommonStageTensorBraidingNaturality | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CommonStageTensorLineCoherenceNaturality | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CommonStageTensorRightUnitorNaturality | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CommonTensorBraidingNaturality | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CompletedConstantRightUnit | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CompositionTensorMate | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ConstantTwistCoefficientComparison | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteCompositorCounit | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteProductNormalForm | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteProperProductMaps | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteProperProductTranspose | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteTateSourceStructuralCoherence | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FiniteTripleProductDefinitions | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FourierTrivialCharacterUnit | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FrobeniusEvaluationProjectionCoherence | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.InverseContravariantBidual | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.LisseLocalizationData | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.MiddleExchangeProjectionBaseChange | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.OperationCoefficientActionData | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.OrdinaryDerivedProductLegTransposes | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.PodCompletionReindexCoefficientTransition | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.PodCompletionReindexCoherence | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.PodMixedSupportCupProduct | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.PodReindexingHomCoefficientDescent | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.ProperProductCounitTranspose | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.RationalTwistedPullbackCompositor | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.RegularCoefficientCoherentReduction | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.RelativeKunnethClosedFibre | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.RelativeProductFactors | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.SemilinearExchangeCubeData | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.TateTwistIntegralLines | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilData | unclaimed | Unchanged interface; no adaptation. |
| Sheaf.SixFunctors.OpenBaseChangeSquareData | unclaimed | Unchanged interface; no adaptation. |

## Validation

The complete item compiled through `lcompile.py` in 53.5 seconds, exit 0.
All eight original named theorem holes remain, with zero added holes.
No diagnostic options, output commands or temporary Lean modules are delivered.

## Status

ready for independent review
