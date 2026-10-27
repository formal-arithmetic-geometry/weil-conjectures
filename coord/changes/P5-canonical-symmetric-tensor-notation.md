# AlgebraicGeometry.SymmetricAlgebraSheaf.gradedRestriction_isGradedBaseChangeAlong

## Reason

Filling the two well-definedness proofs requires tensor-product notation in private helpers
and in the base-change proof. The static interface checker records the added
`open scoped TensorProduct` command as an interface change. This command activates existing
notation in this file; it changes no exported declaration, instance, attribute, definition,
public import, or target statement. All newly imported modules are private proof imports.

## Old

```lean
namespace AlgebraicGeometry.SymmetricAlgebraSheaf
```

The namespace previously had no `open scoped TensorProduct` command.

## New

```lean
namespace AlgebraicGeometry.SymmetricAlgebraSheaf

open scoped TensorProduct
```

Both existing theorem statements and all existing public definition bodies stay verbatim.
The theorem proofs are complete, and the remaining added helper declaration is private and
proved. No module held by another group is edited.

## Users

The table lists the complete transitive downstream set reported by the source import graph.
There is no consumer type or semantic change: scoped notation activation in this file does
not modify another file's scope. Thus consumer adaptation is unnecessary. The independent
reader can inspect the unchanged public signatures and definitions directly in the diff.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.AlgebraicModuliStack | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.AlgebraicStackOpenDmLocus | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.AlterationCartierSubboundary | V8 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.BlowupReesSymmetricPresentation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.CoarseModuliOpenRestriction | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.CommonMarkedNodalModel | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.CompleteFlagBundle | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.CoverNestedCartierPreparation | V9 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.StableModificationUniquenessNormal | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationCommonStrictSemistableRefinement | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ValuationStableReduction | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.CurveStackInfinitesimalDmLocus | S5 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DMGeometricInertiaTrivial | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DMIsomSpaceUnramified | K1 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DeJongGeometricallyIrreducibleTower | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DmCoarseProperLocallyQuasiFinite | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DmFiniteNormalizationCharts | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DmOpenFiniteEtalePermanence | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DmPointStabilizer | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.DmStackMorphismProperties | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ElementaryContractionEvaluation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantCurvePencil | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantFlatCurvePreparation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantMarkedPlurinodalFieldAlteration | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantSingleCurveNodalReduction | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.EquivariantSmoothGaloisModel | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ExcellentBaseMarkedSemistableCurve | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteGradedProjProjective | E9 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteStackSchemeTests | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteTypeTorsionUniversalStar | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.FlatificationHorizontalCurvePair | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.FormalModuliQuotient | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberGlobalSNCAlteration | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberStrictLocalTorsionBound | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.GloballyGeneratedProjectiveBundle | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse | S9 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.IntegralBlowupProjectiveGeometry | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback | G3 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.MarkedNodalInfinitesimalFields | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ModuliChartNormalization | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ModuliNormalizationTests | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ModuliStackProperties | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.NodalCurveStackSmooth | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.NodalLogCanonicalReconstruction | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.NodalLogDualizingPullback | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.NodalTraitRegularization | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.OpenModuliSubstack | K9 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.PlurinodalAlteration | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.PointBlowupFibreDefects | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleBaseChange | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleComposition | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateGeometry | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleCoordinateSubschemes | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleQuotientGeometry | X5 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleTautologicalGeometry | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveStablePointedLevelParameter | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFibrewiseAmpleProjective | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperPairRadicialPreparation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperRelativeAmpleProjectiveBundle | X7 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.RelativeAmpleVeryAmple | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.RelativeProjInvertibleTwist | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.RelativelyVeryAmple | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.RepresentableFiniteStackProperties | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.SectionIdealProjExpansion | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.SemilinearSylowGoodComponents | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.SemistableLogPluricanonicalLattices | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveAbelianLevelRigidification | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StableAbelianLevelNormalization | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StableFiberCurve | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StableLevelVersalBranchFreeness | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StableModificationFlatCurvePair | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StablePointedCurve | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StablePointedGenericExtension | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids | M7 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StableVersalLevelChart | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.StackProperLocallyQuasiFiniteComposition | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.SteinSmoothGenericCurve | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.SymmetricProjTautologicalCharts | J2 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.TenCanonicalHilbertParameter | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.UnpointedLevelNormalizationProjectivity | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.UnpointedStableCoarseProjective | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.UnramifiedDiagonalEtaleAtlas | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationContractedComponentInclusion | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalBlowdown | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationExceptionalClosedImageCriterion | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationSemistableStableContraction | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.VectorProjectiveCompletion | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.VectorProjectivePresentation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.AlgebraicGeometry.VeryAmpleFiniteTypeRealization | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.GoodOrientedNearbyKunneth | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.LineZeroGeometry | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.NearbyCyclesDimensionBound | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.NearbyFiniteBaseDescent | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.OrgogozoGoodModification | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.OrientedClosedBaseExtension | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.OrientedNearbyStrictLocalDescription | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.PlurinodalProperHypercover | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.PsiGoodOrientedCohomologyStrata | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.TraitNearbyBaseChange | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.Paper.VectorFrameIntegrationSiteDescent | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.AmpleNeighbourhood | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.BoundedConstructibleTransport | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.BoundedDimensionProjectiveLocalModel | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ExceptionalComponentSpecialization | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.FiniteCoverTubeComparison | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.FiniteProjectiveEnvelope | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.GabberNearbyCycleDimensionBound | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap | N2 | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ProjectiveBundleProper | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ProjectiveBundleSeparated | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.PsiProperSurjectiveConstructibility | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.SemistableModificationFibreContractions | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.SemistableNormalTargetFactorization | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.SmoothTargetModificationExceptionalTree | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.TemkinStableModification | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ValuationCurveProjectivePreparation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ValuationExceptionalLocalCriterion | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ValuationMarkingSemistableSeparation | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ValuationModificationProperCompletion | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ValuationNormalizedGraphModel | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |
| Sheaf.TraceFormula.ValuationSemistableDominatesStable | unclaimed | No adaptation: signatures, instances and public definitions unchanged. |

## Status

landed 20261023T131711-L-2140364 2026-10-23 (merge of deliver/P5/Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra)
