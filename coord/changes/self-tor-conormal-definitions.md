# selfTor conormal foundational declarations

## Reason
The existence and uniqueness statements must import the concrete normalization predicate
without an import cycle through their parent theorem. Move its two definitions into
publicly re-exported modules. The declaration names, types and definition bodies are
identical. No mathematical statement or target interpretation changes.

## Old
The following declarations were in Sheaf.RingTheory.SelfTorConormalComparison:

```lean
noncomputable abbrev conormalExteriorModule (A : Type u) [CommRing A]
    (I : Ideal A) (n : ℕ) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
    (ModuleCat.of (A ⧸ I) (⋀[A ⧸ I]^n I.Cotangent))

def IsSelfTorConormalComparison (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (c : conormalExteriorModule A I n ⟶
      ((Tor' (ModuleCat.{u} A) n).obj (ModuleCat.of A (A ⧸ I))).obj
        (ModuleCat.of A (A ⧸ I))) : Prop :=
  ∀ (r : ℕ) (g : Fin r → I) (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (a : ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A)) ⟶ P.complex),
    a.f 0 ≫ P.π.f 0 =
      ModuleCat.ofHom (I.mkQ.comp
        (exteriorPower.zeroEquiv A (Fin r →₀ A)).toLinearMap) →
    let K := ExteriorAlgebra.koszulComplex A r (fun j ↦ (g j : A))
    let T := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    ∀ (v : Fin n → (Fin r →₀ A)) (z : (T.obj K).cycles n),
      (T.obj K).iCycles n z =
        (exteriorPower.ιMulti A n v) ⊗ₜ[A] (1 : A ⧸ I) →
      (P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom
          (c (exteriorPower.ιMulti (A ⧸ I) n
            (fun j ↦ I.toCotangent (Finsupp.linearCombination A g (v j))))) =
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.down ℕ) n).map
          (T.map a)) ((T.obj K).homologyπ n z)

```

## New
The exact same declarations and bodies above are now declared in
Sheaf.RingTheory.ConormalExteriorModule and
Sheaf.RingTheory.SelfTorConormalComparisonPredicate, respectively. The parent
publicly imports the predicate module, which publicly imports the exterior module.
Only the existence and uniqueness modules are proof imports of the parent.

## Users
Source inspection with tools/downstream.py --uses found that only the item itself
mentions the moved names. Every downstream module retains the same accessible
constants, types, bodies and required public imports. No forced adaptation is needed.
The table includes the complete transitive downstream list produced by that tool;
none of those modules is edited. Holders below are not consulted because no edits
or adaptations to their files are made.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.SelfTorConormalComparison | V4 | same declarations re-exported, target signature unchanged |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GenusInvariant | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDual | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionAlgebraDualHomology | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionDualizing | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtPullback | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheaf | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulRegularImmersionExtSheafNonnegative | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalComparisonSurjection | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalCompatibleCover | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalAlignment | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalLocalComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulSelfExtConormalNestedCharts | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.ClosedFiberPowerSeriesTest | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.EnlargeOpenFiniteEtaleModel | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalDepthTwoPurity | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.LocalFiniteEtaleModelOverlap | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointLocalSection | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoClosedFiberFlat | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoEtaleExtension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFiniteFlat | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.SmoothLocalDepthTwoFinitePurity | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.StalkFiniteEtaleModel | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationEtale | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SelfTorConormalDualChart | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SelfTorConormalDualChartIso | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.TorsionAssembly | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.Paper.GaloisLisseRepresentations | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.Paper.IntegralCoverTrivialCohomology | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| Sheaf.RingTheory.SelfTorConormalRegularIso | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| TargetsCheck | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.AffineSpace | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.Defs | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.Inversion | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.Perverse | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.Properties | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.Properties.BaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.FourierTransform.Properties.Stalk | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Gabber | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.Integral.BaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | not consulted (no adaptation) | same public definitions and signatures, no semantic change |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | not consulted (no adaptation) | same public definitions and signatures, no semantic change |

## Status
landed 20261013T201812-L-3978170 2026-10-13 (merge of deliver/V4/Sheaf.RingTheory.SelfTorConormalComparison)
