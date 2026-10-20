# Sheaf.Paper.GeoCartierExponentIndependence proof-scope commands

## Reason

Stage-3 preflight requests a command-environment change record for the local
reducibility attribute and proof-scoped `omit` / `set_option` commands in the new
private helpers. These commands support the completed proof. In particular,
typeclass search was repeatedly expanding the chosen constant-sheafification
adjoint when comparing the two coefficient rings; the local attribute keeps
this functor abstract and the proof uses its existing functor API.

The added helpers are private and proved. All existing public declarations,
definition bodies, public imports and target statements retain their original
signatures and meanings. The local reducibility attribute is scoped to this
file's section and is not exported to importers. No source-library file changes.

## Old

The original global command context was:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
universe u v r wZ wM wN
open CategoryTheory CategoryTheory.Limits
```

There was no local attribute command for `constantSheaf` or `presheafToSheaf`,
and the item theorem
had the same signature with a `sorry` proof.

## New

The same original commands remain. The additional local command is:

```lean
attribute [local irreducible] constantSheaf presheafToSheaf
```

The sheafification functors are used through their existing functor APIs. Their
chosen-adjoint constructions are kept abstract locally, avoiding repeated expansion
when comparing section types and generating compiled artifacts. The artifact-producing
compile passes in 33.7 seconds, and the unchanged direct consumer passes in 52.9 seconds.

The new private coherence and scalar-unit lemmas use declaration-scoped
`set_option backward.isDefEq.respectTransparency false in` where needed. Their
`omit ... in` commands remove unused derived-category section parameters only
from those private helpers. Explicit localization universes are annotations on
local lets in the proof. The main theorem uses the normal unification settings.
None of these commands adds an exported instance, notation or attribute.
There are no diagnostic, profiler or heartbeat-limit overrides in the delivery.

## Users

`tools/downstream.py Sheaf.Paper.GeoCartierExponentIndependence --uses
geoCartier_exponent_independence restrictionComp transitivity ordinarySingle`
reports 654 transitive downstream modules at this snapshot, and no textual use
of these declarations outside the item. The sole direct importer is
`Sheaf.AlgebraicGeometry.GeoCartierCycleClass`, which retains its existing
statements and needs no adaptation. The complete transitive list follows;
holders are from the synchronized claim records, and no consumer is edited.
No target statement or meaning is reopened because no public mathematical
interface changes.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineLinearActionFamily | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearActionRigidity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearExchangeCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearTraceAction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineLinearUniversalAction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction | M4 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineSpaceTopTrace | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLineLocalization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineTraceLinePurity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AmbientAffineTranslationTrace | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierReductionSiteComparison | N1 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals | G5 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | C5 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoCartierCycleClass | T3 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeoP1Cohomology | W3 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction | B2 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition | A6 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer | B3 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals | A7 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineFullAdjunction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineTrace | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedCartierBoundaryExistence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorBundleIntegration | F1 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.VectorIntegrationMate | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AdmissibleVerdierExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AffineSpaceRationalInduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerGeometricComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerSectionCoordinates | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerShriekInterfaces | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoefficientTowerTransitionCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTower | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationCoherenceCocycle | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationLocalizing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompactificationRefinementLocalizing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperFiniteness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperHeartFiniteness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClProperLowerTail | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCoefficientExtension | T5 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactScalar | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeCompactSupportComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteFreeScalarProjection | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FixedFinitePositiveCoefficientTwist | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.GeoCartierExponentIndependence | Y3 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.GlobalVerdierDuality | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | C2 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralProperProjectionFormula | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.InterchangeProperPasting | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizingLowerShriekCompositionModel | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.MateOpenRestriction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.MixedReductionUnit | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.NonrationalCompositionSeed | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectionFiniteReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperLocalizingAdmissibleCoefficients | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperLocalizingContinuousAlgCl | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameClass | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityFrameKummer | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityFramePrincipalBoundary | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalRestrictionGlue | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalTensorSymmetry | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.RestrictionLocal | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ScalarExchangeConstituents | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TensorAdjunctionExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityBaseChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityDirectSum | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityNormalization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.VerdierExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionExceptional | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionTransition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.NormalizedTowerTensorEvaluation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Targets.PoincareUncurry | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| TargetsCheck | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.SmoothPurity.Defs | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Basic | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Statement | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed in synced records | Proof-local commands only; public interface unchanged; no adaptation. |

## Status

landed 20261020T211901-L-3514574 2026-10-20 (merge of deliver/Y3/Sheaf.Paper.GeoCartierExponentIndependence)
