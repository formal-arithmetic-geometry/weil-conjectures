# Scalar-extension compilation partitions

## Reason

The current monolithic module fails the per-file compilation limit. Profiling
isolates repeated elaboration around the ambient scalar-shift instance and the
nested chosen derived-tensor construction. An optimized monolithic diagnostic
still reaches the 120-second stop. The existing self-contained sections are
therefore moved to separate modules after introducing a local unfolding boundary.
The explicit worker brief permits this optimization followed by section splitting.

## Old

All 93 public declarations were declared in `Sheaf.Paper.PbcScalarExtension`.
The following instance and inner local attribute were present verbatim:

```lean
instance pbcAmbientScalarShift : (pbcEmbeddingAmbientTensor l E F i T).CommShift ℤ :=
  (pbcAmbientScalarShift_exists l E F i T).exists.choose

section NormalizedScalarAdjunctionShift
attribute [local irreducible] completedAdicDerivedChange pbcDerivedScalarAdjunction
```

## New

The instance has exactly the same signature and body, in
`Sheaf.Paper.PbcScalarAmbientShift`. At the beginning of its `ScalarShift` section,
before elaborating any shift declaration, use:

```lean
attribute [local irreducible] completedAdicDerivedChange
```

The inner scope now contains only the other local attribute:

```lean
section NormalizedScalarAdjunctionShift
attribute [local irreducible] pbcDerivedScalarAdjunction
```

The completed scheme-composition theorem and its private helper remain in the
original module, preserving its existing quotient-compositor dependency route.
The original module publicly imports `Sheaf.Paper.PbcScalarRestriction`, whose
public import chain re-exports all eleven partitions. The original module also
retains all its original public imports. Every original public declaration name,
statement, construction and proof is preserved. Only source locations, proof
imports, blueprint attachments and this local reducibility scope change.
The entry-point also privately imports all extracted sections to preserve the
private helper view used by existing `import all` consumers. A temporary probe
checks all sixty original private helper names through the original import.
No exported reducibility, instance priority, theorem attribute or binder changes.
There are eight existing holes before and after, and no newly named obligation.

DAG records (reviewer FIX, 2026-10-27): the item node `prop-weil-pbc-scalar-extension`
now lists only its two own declarations; the moved companions are owned by the eleven
new `lem-pbc-scalar-*` nodes. The item's statement uses `pbcCoefficientStage`,
`pbcStageTransition` and `pbcStageAssociator` (owned by `lem-pbc-scalar-stage-coherence`),
and its listed `pbcScalarCompletedPull_comp` uses `pbcScalarCompletedPullIso` and
`pbcScalarPreservesComplete` (owned by `lem-pbc-scalar-ambient-operation-comparisons`),
so both nodes are added to the item's `stmt_deps`. No statement text changes.

## Users

This table includes all sixty direct importers and all downstream modules that
textually mention a moved declaration. The latter is the conservative
`downstream.py --uses` criterion, including harmless textual mentions. Statements,
proofs and the public interface are unchanged; the original private helper view
is preserved and all sixty private helpers pass the `import all` probe. No module
outside this item needs adaptation. Holders are those recorded when prepared.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.A1QbarOpenClosedCohomology` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.AdicFibreComparisonCoherence` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.AdicFibreComparisonData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.AdicHeartPullbackFibres` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.AdicNormalizedFibreScalar` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.AdicProperAdjunctionRealization` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.CbcRationalExchangeStage` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.CommonStageCalculus` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.CompletedPullbackFractionDescent` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ContinuousRationalRealizationData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ExceptionalCommonStageDescent` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ExceptionalFieldDescent` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ExchangeFunctoriality` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FdCoefficientComparison` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FdCommonStageComparisonDescent` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FdHomLinearEquivalence` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FdIntegralInverseScalarCocycle` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FdPullbackSignedShiftWordTransport` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FdScalarPullbackRealizationIdentification` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FdScalarRoosComparisonIntertwining` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FdShiftTriangleReflection` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FiniteEtaleAdicCohomology` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FiniteStagePairCategory` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FiniteStageRationalExchangeData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FrameworkPbcComparisonData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FrameworkPbcComparisonSystem` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FrameworkPbcIntegralComparisonLaws` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FrameworkPbcPullbackScalarBridge` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FrameworkPbcRawComparisonData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.FrameworkPbcRawComparisonLaws` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.GeometricFiberQbar` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.IntegralCompactSupportUniformRestriction` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.IntegralScalarHeart` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.IsomorphismPullbackTExactCoefficients` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.MixedCompactSupportExchangeData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.NormalizedCoefficientFamilies` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcAutomorphismTransport` | T7 | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcCoefficientTwists` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcDescentFunctors` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcDescentInterfaces` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcDirectImageCoherentFamily` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcDirectImageFamilyExact` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcDirectImageFamilyShiftCompatible` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcDirectImageStageExact` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcExchangeCompatibleFamily` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcExchangeStageSquare` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcFiniteRawScalarComparison` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcPullbackCoherentFamily` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PbcQbarCategory` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PerAdicCommonStageTruncations` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.QbarCohomologyFiniteLevelComparison` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.QbarCompactSupportBaseChange` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.QbarCompactSupportExchangeModel` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.QbarProperBaseChange` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalDirectImageRealization` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalModuleRealizationFunctor` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalPurityPresentation` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalRealizationPullbackComparison` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalRealizationScalarCoherence` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalScalarBalancedLocalization` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalScalarCompletionUnitSquare` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RationalScalarMixedUnitCancellation` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RealizationAdjointComparisons` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RealizationCompletedPullData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.RealizationScalarFunctor` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.SbcCompletedOperations` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ScalarFibreComponentData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.SemilinearExchangeDescentData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.SfPackageCommonStageTransport` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.SfStrictDirectImageScalarComparison` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.SfStrictDirectImageScalarData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.TateTwistLisseLine` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.TwFrobeniusAction` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.WfTateTwist` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.WfTateTwistCompatibility` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.WholeTowerIntegralPullbackComparison` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.Paper.ZlSfPbcNormalizedHeartModel` | unclaimed | Same re-exported declarations; no adaptation. |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | unclaimed | Same re-exported declarations; no adaptation. |

## Status

landed 20261027T021315-L-2755681 2026-10-27 (merge of deliver/E5/Sheaf.Paper.PbcScalarExtension)
