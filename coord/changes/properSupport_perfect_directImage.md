# AlgebraicGeometry.properSupport_perfect_directImage

## Reason

The prior Lean used derived pullback of G on the new scheme. Tag 0A1D explicitly
uses ordinary termwise pullback, and Tag 0A1H invokes exactly that theorem.
STATEMENT-DISPUTED (prior signature): take R=Z, A=Z[x]/(2x), M=A/(x)=Z,
X=Spec(A), S=Spec(Z), E=O_X, G=M[0], and T=Spec(F2). The support of M is the
closed section x=0, isomorphic to S, so is proper over S. M is finitely presented
and R-flat; f is of finite presentation and qcqs. The free A-resolution of M has
alternating differentials x and 2: ann(x)=(2), ann(2)=(x). Tensoring with
B=A/2A=F2[x] gives differentials x and 0. Thus Tor_2^A(M,B)=B/xB=F2.
The prior right side has nonzero cohomology in degree -2, whereas the left side
is F2[0]. Ordinary pullback gives the correct source statement. No target signature
or definition changes, and the perfectness conjunct is unchanged.

## Old

```lean
theorem properSupport_perfect_directImage
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E)
    (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n)) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      (E ⊗ (DerivedCategory.Q.obj G))) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        Nonempty ((derivedPullback g).obj
            ((schemeDerivedDirectImage f).obj (E ⊗ (DerivedCategory.Q.obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj E ⊗
              (derivedPullback (pullback.fst f g)).obj (DerivedCategory.Q.obj G)))
```

## New

```lean
theorem properSupport_perfect_directImage
    {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : Scheme.IsPerfect X E)
    (G : CochainComplex X.Modules ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n)) :
    Scheme.IsPerfect S ((schemeDerivedDirectImage f).obj
      (E ⊗ (DerivedCategory.Q.obj G))) ∧
      ∀ {T : Scheme.{u}} (g : T ⟶ S),
        Nonempty ((derivedPullback g).obj
            ((schemeDerivedDirectImage f).obj (E ⊗ (DerivedCategory.Q.obj G))) ≅
          (schemeDerivedDirectImage (pullback.snd f g)).obj
            ((derivedPullback (pullback.fst f g)).obj E ⊗
              DerivedCategory.Q.obj
                (((Scheme.Modules.tensorPullback (pullback.fst f g)).mapHomologicalComplex
                  (.up ℤ)).obj G)))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | M2 | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Only direct declaration user; uses .1; unchanged source compiled against correction. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | J1 | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | V2 | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | N1 | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | R1 | Correct ordinary G pullback clause; hypotheses and perfectness unchanged. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | J2 | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| TargetsCheck | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.Defs | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.Properties | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | No declaration use; unchanged signature downstream of the unchanged caller interface. |

The new public import SingleComplexBaseChangeStalkCondition supplies the existing
ordinary pullback additivity instance needed to state Q of the pulled complex.
No existing user is adapted; the sole direct Lean user remains mathematically identical.
Targets depend on the unchanged first clause through this caller and need no new
statement or definition. The second clause was false in the prior Lean and is corrected
to the source, rather than adding a flatness or Tor-independence hypothesis.

## Status

landed 20261013T024044-L-3337853 2026-10-13 (merge of deliver/R1/Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage)
