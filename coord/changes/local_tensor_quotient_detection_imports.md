# AdicCompletion.local_tensor_quotient_detection import interface

## Reason

The statement mentions no adic completion and needs only the tensor product itself,
not the tensor-product maps library. Remove the unused completion import and use
TensorProduct.Basic for the signature. The two newly split supporting theorems are
proof dependencies, imported with plain import. Every existing declaration signature
and visibility remains byte for byte the same. No definition or target meaning changes.

## Old

```lean
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
```

## New

```lean
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.RingTheory.LocalTensorQuotientPowerBound
import Sheaf.RingTheory.LocalTensorQuotientBaseIdealDetection
```

## Users

The source import scan gives one direct importer and 272 transitive importers.
Only Sheaf.RingTheory.CompletionTensorLocalMapsInjective mentions the theorem.
It imports the item with plain import and already publicly imports
Mathlib.RingTheory.AdicCompletion.Algebra itself. It also imports
Sheaf.RingTheory.CompletionTensorQuotientSeparated, which publicly imports
Mathlib.RingTheory.TensorProduct.Maps. Thus both removed imports remain available
in the sole direct user's environment through its other imports. Its statements,
definitions, and visibility do not change, so indirect users do not change either.
No adaptation is included or necessary. No target review is reopened because no
statement or definition changed.

An additional scratch compile of the unchanged direct importer against the new
modules reached the lcompile.py 60-second timeout without a compiler error; it is
not claimed as a successful proof recompilation. The delivered item and both new
modules passed their file compiles and axiom probes. The import-availability
argument above establishes the lack of a forced interface adaptation; the
maintainer's global build remains the verification of the downstream proof.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleNormalComponents | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleHenselianGRingStage | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | C3 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.GenericFibreHomExtension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.GenericFibreHomExtensionExistence | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.GenericFibreTorsorIdentity | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFiniteStageDiagram | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFiniteStageUniversal | D2 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalNoetherianRefinement | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometry | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionSource | R3 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFinite | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | Y2 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.AdjoinSingletonLocalUnramified | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.AlgebraicMonogenicNagataDomainN2 | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.CompleteLocalGRing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.CompletionAtQuasiFinitePrime | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.CompletionAtQuasiFinitePrimeSplit | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.CompletionFiniteExtension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.CompletionFiniteExtensionDecomposition | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.CompletionFiniteQuotient | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.CompletionFiniteQuotientData | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.CompletionTensorLocalMapsInjective | unclaimed | Direct importer; removed imports supplied independently; unchanged statement and proof. |
| Sheaf.RingTheory.EtaleColimitNormalLocalDomain | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.EtaleNormalRing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.FiniteCompletionFactorIdempotent | V3 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.FiniteOverCompleteLocalProduct | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.FiniteSubringGenericFormalFiber | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.FiniteTypeGRing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.FiniteTypeGRingAux | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.FiniteTypeIntGRing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.FormalFibreQuasiFiniteAscent | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.GRingMaximalIdealComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.GRingMaximalIdealCriterion | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.GenericFormalFiberFiniteSubringBase | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.GenericFormalFiberPurelyInseparableRegular | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.GenericFormalFiberPurelyInseparableRegularAux | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.HenselizationPairGRing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.HenselizationPairGRingCore | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.IsAnalyticallyUnramifiedOfIsNagataRing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.IsN1AdjoinSingleton | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.MonogenicNagataDomainN2 | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.NagataUniversallyJapanese | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.NormalFiniteTypeSubalgebraExtension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialCompleteLocalGenericFibre | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialCompleteLocalNonzeroFibreCharZero | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialCompleteLocalNonzeroFibreCharZeroReduction | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialFormalFiber | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialFormalFiberFiniteReduction | J2 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialFormalFiberGeometric | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialGRingComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PolynomialNagata | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PowerSeriesPolynomialFormalFiber | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PowerSeriesPolynomialFormalFiberDegreePPresentation | J2 | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.PowerSeriesPolynomialFormalFiberGeometricComponent | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.RegularPowerSeriesGenericFormalFiber | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.SmoothNormalDomainApproximation | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| Sheaf.RingTheory.SmoothNormalRing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| TargetsCheck | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Indirect user; direct importer exports unchanged declarations; no adaptation. |

## Status

landed 20261012T225328-L-1812457 2026-10-12 (merge of deliver/S1/Sheaf.RingTheory.LocalTensorQuotientDetection)
