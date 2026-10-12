# AlgebraicGeometry.exists_local_section_of_shortExact_finiteLocallyFree

## Reason

The original Lean signature is false: `restrict(g) ≫ s = 𝟙` asserts a left inverse
on the middle term. For the split exact sequence 0 → 𝒪 → 𝒪² → 𝒪 → 0 over
Spec of a nonzero field, the projection has nonzero kernel on every neighborhood
of its point and admits no such left inverse. The node and its cited source require
`q ∘ s = id` on the quotient, which Lean writes `s ≫ restrict(g) = 𝟙`.
This corrects a stage-2 translation error without changing the mathematical node.
The original reviewer read `≫` in the wrong direction.

## Old

```lean
theorem exists_local_section_of_shortExact_finiteLocallyFree
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {d : ℕ} (hE₃ : S.X₃.IsFiniteLocallyFreeOfRank d) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ s : (Scheme.Modules.restrictFunctor U.ι).obj S.X₃ ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj S.X₂,
        (Scheme.Modules.restrictFunctor U.ι).map S.g ≫ s = 𝟙 _
```

## New

```lean
theorem exists_local_section_of_shortExact_finiteLocallyFree
    {X : Scheme.{u}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    {d : ℕ} (hE₃ : S.X₃.IsFiniteLocallyFreeOfRank d) :
    ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ s : (Scheme.Modules.restrictFunctor U.ι).obj S.X₃ ⟶
          (Scheme.Modules.restrictFunctor U.ι).obj S.X₂,
        s ≫ (Scheme.Modules.restrictFunctor U.ι).map S.g = 𝟙 _
```

All binders, universes, visibility, and the declaration name are retained.
The corrected statement has a complete proof and no new holes.

## Users

`tools/downstream.py` finds 304 transitive importers. A whole-word source
search finds no use of the declaration outside its own definition. In particular,
its sole direct importer has an untouched `sorry` and needs no adaptation.
No definition changes, so none of the target statements changes meaning.
No module besides the item is delivered or adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | T1 | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FibreCartierLocal | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLift | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | J1 | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExactExists | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Modules.LocalSplittingFiniteFree | N2 | Direct proof importer; does not use the declaration; compiles unchanged. |
| Sheaf.AlgebraicGeometry.NonzeroSectionIntegralCartier | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | N2 | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | J2 | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.AlgebraicGeometry.ValuationZeroSectionRelativeCartier | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| TargetsCheck | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | K2 | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Gabber | N2 | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive importer; no use of this declaration; no statement or definition changes. |

## Status

landed 20261012T202232-L-701922 2026-10-12 (merge of deliver/C2/Sheaf.AlgebraicGeometry.LocalSectionQuotientFiniteFree)
