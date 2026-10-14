# mapExtendHomologyIso

## Reason

Upstream review #1424 requires using HomologicalComplex.mapExtendX/mapExtendIso
rather than duplicate implementations. The supplied base already removed those
duplicates. The same review explicitly suggests exposing the canonical data behind
mapExtendHomology_nonempty_iso as a definition. Complete that API repair: construct
the composite directly, and package it in the existing existence theorem.

## Old

No mapExtendHomologyIso declaration. The existence theorem directly constructs
its witness from homologyFunctor.mapIso (HomologicalComplex.mapExtendIso ...)
and extendHomologyIso. ExtendMap was imported only for a proof.

Verbatim old import and declaration:

```lean
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap

theorem mapExtendHomology_nonempty_iso
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (q : ℕ) :
    Nonempty
      (((E.mapHomologicalComplex (.up ℤ)).obj
          (K.extend ComplexShape.embeddingUpNat)).homology (q : ℤ) ≅
        ((E.mapHomologicalComplex (.up ℕ)).obj K).homology q) := by
  exact ⟨(HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).mapIso
      (HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat E) ≪≫
    ((E.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl⟩
```

## New

```lean
def mapExtendHomologyIso
    {D : Type u} [Category.{v} D] [Abelian D]
    {B : Type u'} [Category.{v'} B] [Abelian B]
    (E : D ⥤ B) [E.Additive] (K : CochainComplex D ℕ) (q : ℕ) :
    ((E.mapHomologicalComplex (.up ℤ)).obj
        (K.extend ComplexShape.embeddingUpNat)).homology (q : ℤ) ≅
      ((E.mapHomologicalComplex (.up ℕ)).obj K).homology q :=
  (HomologicalComplex.homologyFunctor B (.up ℤ) (q : ℤ)).mapIso
      (HomologicalComplex.mapExtendIso K ComplexShape.embeddingUpNat E) ≪≫
    ((E.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl
```

ExtendMap is now publicly imported because the public data construction uses it.
mapExtendHomology_nonempty_iso keeps its exact signature and visibility, with
proof `exact ⟨mapExtendHomologyIso E K q⟩`. No data is chosen from an existence
proof. No target statement or definition used by a target changes its meaning.

## Users

No module is adapted or requires adaptation; group ownership is irrelevant to
these read-only consumers. Below is the full downstream.py output module set,
including transitive importers. The sole direct importer and declaration caller
is Sheaf.Paper.FreeRepresentableHomotopyHomology.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyBaseChangeSquare | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyLinearBaseChange | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyPullbackComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyTensorKernel | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyTensorSurjective | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveScalarBaseChange | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierBaseChangeModel | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.CanonicalAdditiveCohomologyComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleTensorPositiveDirectImageVanishing | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleZariskiCohomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.PositiveDirectImageOfObjectAcyclic | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not adapted | Existing signature and meaning unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.EtaleObjectCohomologyStalkComplex | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.FreeRepresentableHomotopyHomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.GabberCriterion | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.LocalStalkSectionsAffineVanishing | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.LocalStalkSectionsComparisonMap | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.LocalStalkSectionsDescentEquality | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.LocalStalkSectionsDescentSections | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ObjectCohomologyPresheafResolution | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.PushedResolutionPositiveHomologyZero | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.StrictHenselianCohomologyLocallyZero | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.StrictHenselianStalkSectionsComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.StrictHenselianStalkSectionsComparisonIso | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.StrictHenselianStalkSectionsEpi | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ZariskiEtaleCanonicalLeray | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ZariskiEtalePushedResolution | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ZariskiEtalePushedResolutionQuasiIso | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ZariskiEtaleResolutionCocycleEquivalences | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ZariskiEtaleResolutionCocycleHomology | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ZariskiEtaleResolutionComparisonExists | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ZariskiEtaleResolutionHomologyDataExists | not adapted | Existing signature and meaning unchanged. |
| Sheaf.Paper.ZariskiEtaleResolutionMap | not adapted | Existing signature and meaning unchanged. |
| TargetsCheck | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.Defs | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.Inversion | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.Perverse | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.Properties | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not adapted | Existing signature and meaning unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not adapted | Existing signature and meaning unchanged. |

## Status

landed 20261014T041059-L-1059964 2026-10-14 (merge of deliver/W4/Sheaf.CategoryTheory.MapExtendHomology)
