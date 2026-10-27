# RingHom.exists_local_module_arrow_noetherian_descent

## Reason

Stage-3 preflight classifies changes to commands as potentially visible. The proof needs
`ChangeOfRings` notation for explicit ring-hom tensor products. The original named binders
`hModM` and `hModN` are used implicitly in the existential statement; suppress their unused
variable warning only for this declaration, preserving the complete signature verbatim.
Both commands are local elaboration settings, not a change in mathematical meaning.
No public declaration or import changes. All new helpers are private and proved.
The returned packet's duplicate countability and representative/eventual-zero colimit
helpers are removed. Mathlib smallness and underlying-type filtered colimit APIs replace
them. The proved private lifting helper accepts an arbitrary filtered category and a
colimit of underlying types; it changes no public interface. No source-library signature,
visibility, import or definition is changed.

## Old

```lean
open scoped TensorProduct
```

The theorem previously had no scoped linter override.

## New

```lean
open scoped TensorProduct ChangeOfRings
```

Immediately before the original theorem docstring:

```lean
set_option linter.unusedVariables false in
```

The theorem's full statement is unchanged, as are all existing public imports. Added proof
imports are private. There are no new public definitions, instances or attributes.

## Users

`tools/downstream.py Sheaf.RingTheory.LocalModuleArrowNoetherianDescent --uses
RingHom.exists_local_module_arrow_noetherian_descent` reports 141 downstream modules (refreshed during this repair).
The only direct theorem user is `Sheaf.RingTheory.LocalEssentiallyFinitePresentationModInjective`.
The module itself is also listed by the declaration-use search. Every module below retains
exactly the same theorem type and definitions; no target meaning is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.LocalModuleArrowNoetherianDescent | F8 | Proof completed; signature preserved |
| Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.AdjunctionCotangentDeterminantNormalization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.CoefficientTestSequencePropagation | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.CommonPowerHilbertMarking | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ValuationMarkedStrictification | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.DvrNodalEtaleLocalForm | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.EmbeddedResolutionAmbientComparison | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleNearRegularCoordinateFibre | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.EtaleSourceAdjunctionLine | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteAfterBlowup | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteEquivariantQuasiSplitNodalFibres | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FiniteTypeFlatEtaleNeighborhood | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FlatRelativeAssociatedSpecialization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FlatteningModuleByAdmissibleBlowup | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FormalPlaneAdjunctionLattice | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FreeCharacteristicRelativeNCCriterion | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.FunctorialFanDesingularization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.GenericFreeBlowup | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.HighGenusHomClosure | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertSamuelLocalPresentations | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertSamuelReachableLevels | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.HilbertSamuelSmoothDimensionProfile | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.LCICurveFundamentalClass | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.MarkedIdealTransverseSuspension | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.MarkedNodalDualizingDegrees | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.MinimalEnvelopeCoefficientComparison | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.ModificationFibreCentreFinite | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.NodalCurveLCICriterion | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.NodalCurveStackSmooth | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.NodalPairProjectiveResolution | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.NodalPointFiniteSeparableSplitting | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.NodalTraitRegularization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.PersistentNodeNormalization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.PointBlowupFibreDefects | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.ResolutionInvariantCalculus | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothFunctorialNormalizedToricDesingularization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothFunctorialOrdinaryResolution | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.SmoothPairLocalCoordinates | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.SpaceNodalLocusBaseChange | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.StableLevelVersalBranchFreeness | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.StableModificationStabilityLocus | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.StrictlySemistableCurve | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.StrictlySemistableModelNormal | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.UnpointedLevelNormalizationProjectivity | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationCurveFiniteNormalization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | No interface or statement change; no adaptation |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.AlterationBlowupFinite | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.AlterationFiniteRefinement | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.ModificationClosedImageLifting | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.PurityDivisorClass | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No interface or statement change; no adaptation |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No interface or statement change; no adaptation |
| Sheaf.RingTheory.LocalEssentiallyFinitePresentationModInjective | unclaimed | No interface or statement change; no adaptation |
| Sheaf.RingTheory.RelativeRegularEquationsBaseChange | unclaimed | No interface or statement change; no adaptation |
| Sheaf.RingTheory.ValuationFibreInjectiveSourcePresentation | unclaimed | No interface or statement change; no adaptation |
| Sheaf.SecTraceFormula.SmoothCenterBlowupGeometry | unclaimed | No interface or statement change; no adaptation |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No interface or statement change; no adaptation |
| Sheaf.SixFunctors.TraceFormula.NodalEtaleChart | unclaimed | No interface or statement change; no adaptation |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyEtaleLocalModel | unclaimed | No interface or statement change; no adaptation |
| Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular | unclaimed | No interface or statement change; no adaptation |
| Sheaf.SixFunctors.TraceFormula.NodalLogRegularity | unclaimed | No interface or statement change; no adaptation |
| Sheaf.SixFunctors.TraceFormula.ProjectiveNodalFamilyGeometry | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.BaseModificationComparisonFibreImage | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.CanonicalTwoTermPerfectDeterminant | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.CompletedConormalDeterminantComparison | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ContractedComponentGenericData | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.DivisorialLogChart | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.FiniteEtaFlatification | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.FiniteFibreValuationDomination | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.FlatAssociatedEquidimensional | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.FlatFibreComponentClosureDimension | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.FlatFibreFreeNeighbourhood | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.FlatFiniteTypeDensePresentation | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.FlatFiniteTypeFlatPointLocal | P8 | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.MarkedCurveFiniteTypeModel | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.NoIsolatedContractedFibreComponent | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.NodalChartBoundaryShrinking | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.NodalFamilyNoetherianApproximation | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ReducedFibreModification | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.SingleValuationSemistableExtraction | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.StableCurveDiagramNoetherianModel | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.StableModificationConstructibility | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.StableModificationSpreading | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.StableModificationStabilityFieldDescent | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationFiniteModuleInjectivity | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationHorizontalCurveModels | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationSmoothBranchesStrictChart | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationStrictSemistableCofinality | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationStrictSemistableLocalUniformization | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuationSymmetricNodalBlowup | unclaimed | No interface or statement change; no adaptation |
| Sheaf.TraceFormula.ValuativeDominationEtaNormal | unclaimed | No interface or statement change; no adaptation |

## Status

landed 20261023T231140-L-3552975 2026-10-23 (merge of deliver/F8/Sheaf.RingTheory.LocalModuleArrowNoetherianDescent)
