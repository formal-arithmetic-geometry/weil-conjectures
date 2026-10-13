# exists_finite_cover_adjoin_singleton_core import pruning

## Reason

The structural finite cover does not use analytic unramifiedness. Remove that unused
public import. The Noetherian-localization instance from Mathlib's Localization.Submodule
is used only by the proof, so make it a plain proof import. The core theorem's elaborated
signature and visibility are unchanged. No definition or target statement changes.

## Old

```lean
public import Sheaf.RingTheory.AnalyticallyUnramified
public import Sheaf.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.RingTheory.FiniteOverNagata
import Sheaf.RingTheory.JapaneseDomain
import Sheaf.RingTheory.NagataLocalization
```

## New

```lean
public import Sheaf.RingTheory.NagataRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.AdjoinSingletonSplittingCover
```

## Users

The sole direct importer is `Sheaf.RingTheory.AdjoinSingletonMaximalFiniteCover`. It
already publicly imports both `Sheaf.RingTheory.AnalyticallyUnramified` and
`Mathlib.RingTheory.Localization.Submodule`. Thus its statements and proofs retain the
same available declarations and instances. All other downstream modules pass through
that module and retain the same imports. The two textual uses reported by
`tools/downstream.py --uses exists_finite_cover_adjoin_singleton_core` are the core
itself and this direct importer. No existing module other than the item is edited.
No target definition or statement meaning changes, and no target statement review is
reopened. The following is the complete transitive downstream list, with holders from
this machine's claim files; all have unchanged signatures and need no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleColimitCocone | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleGenerationFiniteType | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | H2 | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardNoetherian | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralMapFactorization | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleModuleIntegralStalkEmbedding | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleModuleNormalizedGenericData | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleModuleSheafColimit | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleRestrictionClass | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ConstructibleSubobjectPresentation | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleApproximationAssertions | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.PrimeConstructiblePullback | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | V1 | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.EtaleNormalComponents | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | E2 | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalTraitPurity | U1 | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.GenericFibreActionExtension | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.GenericFibreHomExtension | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.GenericFibreHomExtensionExistence | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.GenericFibreTorsorIdentity | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFiniteStageDiagram | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFiniteStageUniversal | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.NormalNoetherianRefinement | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometry | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionFlat | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationDepthTwoSectionSource | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFinite | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationNormalDense | U1 | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationSectionNeighbourhood | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationTraitSectionSource | Y2 | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.NormalGenericConstant | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataCore | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.NormalizedGenericDataWithFactorization | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.AdjoinSingletonMaximalFiniteCover | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.AlgebraicMonogenicNagataDomainN2 | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.EtaleColimitNormalLocalDomain | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.EtaleNormalRing | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.FiniteTypeZDomainNormalizationFinite | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.IsN1AdjoinSingleton | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.MonogenicNagataDomainN2 | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.NagataUniversallyJapanese | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.NormalFiniteTypeSubalgebraExtension | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.PolynomialNagata | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.SmoothNormalDomainApproximation | unclaimed | unchanged signatures; no adaptation needed |
| Sheaf.RingTheory.SmoothNormalRing | unclaimed | unchanged signatures; no adaptation needed |
| TargetsCheck | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Defs | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Inversion | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Perverse | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Properties | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | unchanged signatures; no adaptation needed |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | unchanged signatures; no adaptation needed |

## Status

landed 20261013T004337-L-2510158 2026-10-13 (merge of deliver/V1/Sheaf.RingTheory.AdjoinSingletonFiniteCoverCore)
