# mapExtendHomologyIso method-form application

## Reason

Replace a fully qualified application with Lean's method-form application of the
same upstream declaration. This is an exposed definition-body edit, so preflight
requires this record even though the elaborated construction is unchanged. This
notation change closes no holes and removes no duplicate in the current baseline.

## Old

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
      (K.mapExtendIso ComplexShape.embeddingUpNat E) ≪≫
    ((E.mapHomologicalComplex (.up ℕ)).obj K).extendHomologyIso
      ComplexShape.embeddingUpNat (j := q) rfl
```

## Users

The following lists every downstream module reported by
`python3 tools/downstream.py Sheaf.CategoryTheory.MapExtendHomology --uses mapExtendHomologyIso`.
Only the item itself mentions mapExtendHomologyIso. Other modules use the
unchanged Nonempty theorem or import its closure. No user is adapted: both
applications elaborate to the same upstream constant with the same arguments,
so no public statement, definition meaning, or target meaning changes. Holdings
are immaterial to this delivery because no downstream file is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.MapExtendHomology | T1 | Equivalent exposed construction body. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyBaseChangeSquare | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyLinearBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyPullbackComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyTensorKernel | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyTensorSurjective | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveScalarBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierAdditiveVanishing | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierBaseChangeModel | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.BrauerReductionInjection | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.CanonicalAdditiveCohomologyComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeOne | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReductionUnitsKernelVanishing | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentCohomologyULift | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentSourceComparisonNatural | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleTensorPositiveDirectImageVanishing | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiAbelianPositiveComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiCohomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleZariskiQcohComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.PositiveDirectImageOfObjectAcyclic | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.SecondKummerDivisors | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.EtaleObjectCohomologyStalkComplex | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.FreeRepresentableHomotopyHomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.GabberCriterion | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.LocalStalkSectionsAffineVanishing | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.LocalStalkSectionsComparisonMap | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.LocalStalkSectionsDescentEquality | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.LocalStalkSectionsDescentSections | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ObjectCohomologyPresheafResolution | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.PushedResolutionPositiveHomologyZero | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.StrictHenselianCohomologyLocallyZero | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.StrictHenselianStalkSectionsComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.StrictHenselianStalkSectionsComparisonIso | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.StrictHenselianStalkSectionsEpi | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.StrictHenselianZariskiEtaleComparison | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ZariskiEtaleCanonicalLeray | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ZariskiEtalePushedResolution | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ZariskiEtalePushedResolutionQuasiIso | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionCocycleEquivalences | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionCocycleHomology | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionComparisonExists | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionHomologyDataExists | not adapted | Identical statements and meaning; no adaptation. |
| Sheaf.Paper.ZariskiEtaleResolutionMap | not adapted | Identical statements and meaning; no adaptation. |
| TargetsCheck | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Brauer | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Kummer | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.Defs | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.Properties | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not adapted | Identical statements and meaning; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not adapted | Identical statements and meaning; no adaptation. |

## Status

landed 20261014T045612-L-1574401 2026-10-14 (merge of deliver/T1/Sheaf.CategoryTheory.MapExtendHomology)
