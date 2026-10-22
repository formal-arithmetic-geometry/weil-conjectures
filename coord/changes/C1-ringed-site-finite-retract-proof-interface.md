# Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact proof commands and imports

## Reason

The item now has a complete proof without changing any existing declaration's
signature or any of its three public definitions. Generic finite-Hom and exactness
calculations, coordinate identities, and the canonical bidual calculation are proved
private helpers. Temporary canonical-instance priorities and private instance caches
keep the independent-universe internal-Hom calculations tractable. All new instance
registrations are removed before elaborating the public theorem; all priority and
transparency overrides are local. The commands affect this file's elaboration.

The removed public import is unused by this item's statements and definitions. Each
direct importer already obtains it independently, so none needs adaptation. The
source-library tree is unchanged. No target statement or definition changes meaning.

## Old

The removed import, verbatim:

```lean
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
```

The original option commands, verbatim:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

There were no `FiniteRetractProof` helpers, instance caches, local canonical-instance
priorities, or local irreducibility commands. The sole theorem proof was `by sorry`.
All four public declaration signatures and all three public definition bodies remain
verbatim in the new source.

## New

The unused public import is removed. These proof-only imports are added:

```lean
import all Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackDualFreeChart
import all Sheaf.CategoryTheory.RingedSiteDualityMaps
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Opposite
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
```

The actual option and local attribute commands are:

```lean
set_option autoImplicit false
set_option maxErrors 1
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

attribute [local instance 2000] ModuleCat.isAddCommGroup ModuleCat.isModule
  CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize SheafOfModules.instPreadditive

attribute [local irreducible] finiteRetractCoordinate finiteRetractVector finiteRetractCovector

attribute [-instance] proofHasSheafCompose proofAbelian proofHomContraAdditive
  proofHasFiniteBiproducts proofSectionModule proofHomPreservesZero
```

The last command removes every instance added under `FiniteRetractProof` before the
public theorem. The six private caches are `proofSectionModule` (priority 1300),
`proofHasSheafCompose` (priority 1200), `proofAbelian`, `proofHomContraAdditive`,
`proofHasFiniteBiproducts`, and `proofHomPreservesZero`. Their definitions/proofs use
existing Mathlib structures and the existing internal-Hom functor. They contain no
holes. The cached abelian structure explicitly retains
`SheafOfModules.instPreadditive` as its `toPreadditive` field, so generic exactness
lemmas and concrete zero/composition formulas use that existing native structure
without reducing the sheafification adjunction. The other new definitions are private constructions with proved APIs; no
private helper occurs in an existing public signature or definition body.

`namespace FiniteRetractProof`, its local coefficient-sheaf notation, its `variable
(R)` command, and the later `open FiniteRetractProof` only organize private proof
code. The scoped Fintype linter option on a private projection lemma affects style
checking only. No limits are raised. There are no new public declarations.

## Users

`tools/downstream.py Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact --uses
finiteRetractCoordinate finiteRetractVector finiteRetractCovector
ringedSite_finite_retract_dual_exact` found 698 transitive importers. The only textual
users outside the item are its three direct importers, and they use only the main
theorem. None is edited. Their remaining import routes to the removed module are:

- `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom`: `Sheaf.CategoryTheory.RingedSiteDualityMaps` → `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `Sheaf.Algebra.Homology.SplitPerfectDualTorWindow`: `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses` → `Sheaf.Paper.StrictPerfectPackageOnSite` → `Sheaf.Paper.StrictPerfectCoefficientPackage` → `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `Sheaf.Paper.ScalarPerfectDualRealization`: `Sheaf.CategoryTheory.ConstantCoefficientScalarExtension` → `Sheaf.Paper.StrictPerfectCoefficientPackage` → `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.

In each route all edges after the first are public imports. The removed item edge
is excluded from the search. Thus each direct importer's existing import context
retains the module independently. Every existing public statement keeps its meaning,
and no transitive importer needs adaptation. The complete downstream list and its
current project claim holders are below (snapshot 2026-10-22). Private helpers have
no external textual users.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom | unclaimed | Public API retained; no adaptation. |
| Sheaf.Algebra.Homology.SitePerfectScalarHomComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Algebra.Homology.SplitPerfectDualTorWindow | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerData | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerDescent | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerNaturality | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedEtaleTransportBounds | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonSectionModel | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | D9 | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | unclaimed | Public API retained; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportedFullSupportProduct | unclaimed | Public API retained; no adaptation. |
| Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact | C1 | Proof closed; existing public declarations unchanged. |
| Sheaf.CategoryTheory.RingedSitePerfectDuality | unclaimed | Public API retained; no adaptation. |
| Sheaf.CategoryTheory.RingedSitePerfectDualityForModel | unclaimed | Public API retained; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Public API retained; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Public API retained; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Public API retained; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Public API retained; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.A1LisseSectionEvaluation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.A1LisseSectionsStalkEvaluation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineCoordinateSupportStalkContinuity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineDiagonalTateCoordinates | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineLineOrdinaryInvariance | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineLinePurityComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineLinePurityCoordinateMaps | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineLinePuritySource | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineSpaceCoordinateBoundaries | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineSpaceThomMap | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AmbTateRootProjectionReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BoundaryComparisonCompositionTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | P2 | Public API retained; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CofinalFiniteReductionConstructibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonStageCompactSupportExactness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonStageTensorLineCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportArrowScalarTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportProjectionFormula | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompactifiedTowerComparisons | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompletedLineComplete | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompletedLineDerived | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CompletedTensorHomTranspose | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConcentratedSupportEtaleTransfer | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstantExtensionCompactComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstantExtensionMixedDescent | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstantGeometricStalkUnit | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ConstructibleProjectionMates | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoordinateGermCohomologyClasses | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoordinateGermConcentrationData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DirectImageChangeRingTranspose | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DualStalkFrobenius | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.DualizingUnitComposite | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FieldTwistInverse | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteCoefficientInputModels | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | N1 | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSiteCoordinates | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSiteCounitProjectionTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSiteTensorProjection | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteStructuralMapsCommShift | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteTypeCoordinateSupportOrientation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteWeilIndPushExact | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.HomFiniteProjective | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ImmersionWeilPullbackLocalBehavior | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralLineDerivedComparisons | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralLinePowerComparisons | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralLineReductionDefinitions | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralLineReductionRestriction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralLineRestrictions | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralProperDirectSums | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralStratumHomFormula | K6 | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.InternalHomPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerRefinement | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocalFrobeniusCoefficientExtension | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocalFrobeniusConjugacyClass | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.LocallyClosedRelativeTransposeNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrientationEtaleCoefficientTwists | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrientationEtaleFamily | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrientationGeometricComparisons | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PfRefinementCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointIdentityAdmissibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointSystemPowerRoosCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointSystemRoosTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointSystemTransportDescent | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointTransportStrictQuotient | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PointWeilHeartFlag | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleAffineLineCounit | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleFrameIntegration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleOrderedIntegration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionIntegration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveCoefficient | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleProjectiveLineTrace | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegration | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProEtaleVectorIntegrationArrows | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProjectionPurityAgreement | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperBaseChangeRational | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperHeartBound | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperOpenBoundaryZero | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurTwistSheafLocallyFree | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityAffineChartExceptionalIdentification | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationInjectivity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityAffineLineSupportStalk | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityCoprojection | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityGysinStructure | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityRelativeKummer | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.QcqsCompactSupportRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.QlbarDirectImageComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RankOneClassicalSupportComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RankOneFiniteKummerCohomology | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RankOneKummerGenerator | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RankOneKummerMonomial | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RationalStalkExact | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RealWeights | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ReducedFrontierMixedGluing | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RelativeSupportBottomDescent | A3 | Public API retained; no adaptation. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ResidueControlledFiniteHoms | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ScalarPerfectDualRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SfCommonStageDirectImage | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SfIntegralPullbackLinearAdjunction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SfProEtaleProjectionFormula | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageAdjunction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SignedLineTensorEquivalence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SitePerfectCoefficientDual | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SitePerfectDualizableHom | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorDatum | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorDualNotation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatum | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorOperationDatumStages | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Z7 | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.StratifiedConstantModelProductBound | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedAffineLineHomotopy | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | P5 | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedHomCocycleNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | B8 | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedProjectiveChern | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SystemClopenTensorCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SystemCompactificationProjectionSubstitution | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.SystemOperationExchangeRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | V9 | Public API retained; no adaptation. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TrfDevissageGeneration | C3 | Public API retained; no adaptation. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TwConventions | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.TwistPreservesFiniteness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.VectorTensorSiteEquations | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilCompactSupportCohomology | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilConstantExtensionFrobenius | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilInternalHomWeil | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | U1 | Public API retained; no adaptation. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | Public API retained; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.ClosedUnitAllStages | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarAssociatorConjugate | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | A2 | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin | unclaimed | Public API retained; no adaptation. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.GeneratorReductionStatement | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationBridgeWords | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationComparisonBridge | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | W4 | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenExternalTensorNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisPullbackNaturality | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Public API retained; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Public API retained; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Public API retained; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Public API retained; no adaptation. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | Public API retained; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | Public API retained; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Public API retained; no adaptation. |

## Status

landed 20261022T020058-L-5399 2026-10-22 (merge of deliver/C1/Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact)
