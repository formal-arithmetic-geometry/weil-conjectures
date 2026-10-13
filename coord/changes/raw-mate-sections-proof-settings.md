# AlgebraicGeometry.Scheme.Modules.flatBaseChangeResolution_rawMate_sections

## Reason

The stage-3 preflight classifies local `attribute` and elaborator-option changes as possibly
visible commands. Record these proof elaboration controls for
`Sheaf.AlgebraicGeometry.FlatPullbackResolutionRawMateSections`. Every existing declaration's
signature and visibility is unchanged; the local irreducibility attributes and file options
are not imported by downstream modules. They prevent incidental unfolding of theta
and resolution-map constructions while checking the new proof. This is a proof-only setting
change, not a mathematical definition or interface change. No forced adaptation is made.

## Old

The existing theorem signature is:

```lean
theorem flatBaseChangeResolution_rawMate_sections {X S S' : Scheme.{uBC}}
    (f : X ⟶ S) (g : S' ⟶ S) [Flat g] {F : X.Modules}
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F))
    (t : I.cocomplex ⟶ ((pushforward (pullback.snd g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex) (p : ℕ) (V : S.Opens) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := ((pushforward (pullback.fst g f)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J.cocomplex
    let U := SheafOfModules.forget S.ringCatSheaf
    let U' := SheafOfModules.forget S'.ringCatSheaf
    let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op V)
    let E' := PresheafOfModules.toPresheaf S'.ringCatSheaf.obj ⋙
      (CategoryTheory.evaluation S'.Opensᵒᵖ AddCommGrpCat.{uBC}).obj (op (g ⁻¹ᵁ V))
    let adj := Classical.choose (exists_tensorPullbackAdjunction g)
    ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso E).hom ≫
        E.map (sectionCohomologyTheta K p) ≫
        Hom.app (adj.homEquiv _ _
          (((K.sc p).mapHomologyIso (tensorPullback g)).inv ≫
            HomologicalComplex.homologyMap (flatBaseChangeResolutionC f g I J t) p)) V =
      HomologicalComplex.homologyMap
        (((RingedSpace.openModuleSections S.toRingedSpace V).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (flatBaseChangeResolutionQ f g I J t)) p ≫
        ((((U'.mapHomologicalComplex (ComplexShape.up ℕ)).obj L).sc p)
          |>.mapHomologyIso E').hom ≫ E'.map (sectionCohomologyTheta L p)
```

The original file set `backward.defeqAttrib.useBackward` to `true`, and contained none of the
new local irreducibility attributes below.

## New

The theorem has exactly the same signature above and now has a complete combining proof.
Only the proof-side elaboration controls are added or adjusted:

```lean
set_option backward.defeqAttrib.useBackward false
attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackMap
attribute [local irreducible] sectionCohomologyTheta
attribute [local irreducible] flatBaseChangeResolutionQ flatBaseChangeResolutionC
```

The new proof imports `Sheaf.AlgebraicGeometry.FlatUnitRawSections` privately. That new module
contains the strictly smaller unit compatibility statement, with its own node and one sorry.
The private raw-section helper is proved using the existing theta naturality theorem via
`import all Sheaf.AlgebraicGeometry.HigherDirectImageResolutionNaturality`. The duplicate
adjoint homology and theta helpers have been deleted. All existing public signatures,
universes and visibility are preserved. Scoped heartbeat limits are used for the
category/functor interface comparisons. Local sheafification irreducibility and the
scoped transparency settings for the deleted theta helper are no longer needed.

## Users

`tools/downstream.py` lists the transitive importers below. Its `--uses` search identifies
`Sheaf.AlgebraicGeometry.FlatPullbackHomologySections` as the only other module that directly
mentions the theorem. Its call remains valid because the signature is unchanged. No downstream
module requires an edit, and no target definition or statement is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.FlatPullbackResolutionRawMateSections | N2 | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | F4 | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionLift | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleCompletionStage | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingComplete | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingEssentialSurjectivity | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescentCore | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionAffineSections | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionIso | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatBaseChangeResolutionSections | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FlatPullbackHomologySections | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineAdjunctionModel | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineData | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineModel | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineRestrictionIso | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineTransport | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalComparisonFlatTransportSquare | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFlatQuotientMateData | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteFibreVanishing | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenFactorization | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteOpenUnitPasting | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFinitePullback | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIso | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoB | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientIsoR | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientMaps | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteQuotientTransition | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotient | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsFiniteSheafQuotientCore | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsLocalDictionary | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsLocalStalkComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalFunctionsStalk | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPull | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullAffineAnnihilation | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FormalSystemsPushPullCore | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistence | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceChowComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProper | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceProperComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedSystem | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.GrothendieckExistenceSystemSupport | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.OrdinaryFlatExchangePrescribedAdjunction | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperFibreIdempotentImageNoetherian | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperNormalizedFibres | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteOverProper | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.AlgebraizeFiniteStructureAlgebra | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraAdjointsConstruct | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraLift | D2 | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureAlgebraOperationsLift | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureMultiplicationLift | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureProductCompatibility | U4 | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureProductCore | U4 | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureProductExists | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureTensorTestsFaithful | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureUnitLift | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.FiniteStructureUnitLiftExistence | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.GaloisLisseRepresentations | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| TargetsCheck | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Public signatures and meaning unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Public signatures and meaning unchanged; no adaptation. |

## Status

landed 20261013T165645-L-1809450 2026-10-13 (merge of deliver/N2/Sheaf.AlgebraicGeometry.FlatPullbackResolutionRawMateSections)
