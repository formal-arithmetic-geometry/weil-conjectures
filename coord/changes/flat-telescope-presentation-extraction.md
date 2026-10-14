# AlgebraicGeometry.isFlatTelescope and flatTelescopeShiftRepresentative

## Reason

The stage-map construction and common-refinement lemma must refer to the same
flat-telescope predicates as the parent theorem without importing that theorem
and creating a cycle. Move the two definitions verbatim into the new public
module `Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, and publicly import it
from their former module. Their names, universes, visibility, types and bodies
are unchanged. No target meaning changes. New stage-map data are explicit sum
and cone constructions, with no choice from an existence theorem.

## Old

In `Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeComparison`:

```lean
/-- A concrete sequential telescope of bounded-above flat complexes.
The transition cone is constructed explicitly; no existence witness supplies its data.
Source: Stacks Project, Tag 06YS, telescope construction.
(blueprint: lem-sc-normalized-flat-telescope-comparison). -/
def isFlatTelescope (Y : Scheme.{u})
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ) : Prop :=
  ∃ (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (t : ∀ n : ℕ, E n ⟶ E (n + 1)),
    (∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) ∧
    (∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) ∧
    CochainComplex.mappingCone (𝟙 (∐ E) -
      Sigma.desc (fun n : ℕ ↦ t n ≫ Sigma.ι E (n + 1))) = P

/-- Homotopy objects represented by flat telescopes or their translates by one.
This predicate records actual representatives and contains no choice of data.
Source: Stacks Project, Tag 06YJ.
(blueprint: lem-sc-normalized-flat-telescope-comparison). -/
def flatTelescopeShiftRepresentative (Y : Scheme.{u})
    (X : HomotopyCategory
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
    isFlatTelescope Y P ∧
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P = X ∨
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)⟦(1 : ℤ)⟧ = X)
```

## New

The exact same declarations above, verbatim, in
`Sheaf.AlgebraicGeometry.FlatTelescopeStageMap`, re-exported by
`public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap` in the original module.
Three duplicate public imports (Flat, HomologicalComplexLimits, MappingCone) are
now reached through this public module. The public import closure still contains
all three modules; this is not a claim of global pruning.

## Users

Both `tools/downstream.py --uses isFlatTelescope` and the analogous predicate
search find only the parent and `NormalizedKFlatRepresentativeComparison` as
textual users. The complete transitive importer inventory is included below.
No module outside the parent is adapted: its original source remains valid
against the public re-export of the byte-identical definitions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeComparison | J2 | proof changed; predicates re-exported unchanged |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | C3 | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | R3 | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShift | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedMonoidalPullbackUnitalShiftKFlatOne | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedPullbackCanonicalTensorShiftOne | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatConeCounitNormalization | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedPullbackKFlatCounitShiftAdjustment | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorShift | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorShiftKFlatOne | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnitShift | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitKFlatCones | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DerivedPullbackTranslatedUnitTriangles | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.NormalizedDerivedPullbackKFlatCounit | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.NormalizedKFlatRepresentativeComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.PerfectImmersionTensorAcrossUniverses | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.PinnedProjectionCounitExactShift | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProjectionComparisonExact | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProjectionComparisonTriangles | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonDiagrams | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonNatural | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonProjection | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonShift | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.RightAdjointTensorComparisonTriangle | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.RightAdjointTensorCompatibleExactStructures | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusLocalizing | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.RightAdjointTensorLocusTriangles | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SmoothProperDiagonalTensorFormula | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | no adaptation; same public predicates and definitions |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | no adaptation; same public predicates and definitions |
| TargetsCheck | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.Defs | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.Inversion | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.Perverse | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.Properties | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | no adaptation; same public predicates and definitions |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | no adaptation; same public predicates and definitions |

## Status

landed 20261014T043531-L-1335547 2026-10-14 (merge of deliver/J2/Sheaf.AlgebraicGeometry.NormalizedFlatTelescopeComparison)
