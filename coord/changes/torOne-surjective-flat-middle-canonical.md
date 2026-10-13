# CategoryTheory.torOne_surjective_flat_middle

## Reason

Repair reviewer X-65165 point 4, returned head 651657a54. The former arbitrary
A-action permits opposite projection actions for R = ℤ, A = 𝔽₂ × 𝔽₂,
M = B = 𝔽₂; its source tensor vanishes while the target does not. A scalar tower
alone cannot identify the action with the canonical coefficient action.
The source, Stacks Tag 00MM, specifies the natural map with the canonical action.

The repair constructs torOneModule by functorial coefficient multiplication,
proves its module laws and scalar tower, constructs torOneCoefficientMap by
applying Tor to the algebra map, and constructs torOneBaseChange as a balanced
tensor lift. Its B-linearity and pure-tensor value are proved without holes.
No existence theorem is used to choose data. The original surjectivity hole stays.
The dispute marker is retained until the repaired interface is delivered.

## Old

```lean
theorem torOne_surjective_flat_middle
    (R : Type u) (A : Type u) (B : Type u) (M : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Module R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M]
    [Module A (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R A))]
    [IsScalarTower R A (((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
      (ModuleCat.of R A))]
    (hflat : Module.Flat A (A ⊗[R] M)) :
    ∃ φ :
        ModuleCat.of R
            ((((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj
              (ModuleCat.of R A)) ⊗[A] B) ⟶
        ((Tor' (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R B),
      Epi φ
```

## New

```lean
theorem torOne_surjective_flat_middle
    (R : Type u) (A : Type u) (B : Type u) (M : Type u)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Module R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module R M]
    (hflat : Module.Flat A (A ⊗[R] M)) :
    letI := torOneModule R M A
    letI := torOneTensorModule R M A B
    letI := torTowerAlgebra R A B
    letI := torOneModule R M B
    Function.Surjective (torOneBaseChange R M A B)
```

New constructed data and their proved laws are all in the item's module:
`CategoryTheory.TorOne` (abbreviation of the existing Mathlib Tor object),
`CategoryTheory.torTowerAlgebra`, `CategoryTheory.torCoefficientMul`,
`CategoryTheory.torOneModule`, `CategoryTheory.torCoefficientMap`,
`CategoryTheory.torOneCoefficientMap`, `CategoryTheory.torOneTensorModule`,
`CategoryTheory.torOnePairing`, and `CategoryTheory.torOneBaseChange`.
`torOneSecondAdditive` and `torOneSecondLinear` supply the proved functor laws;
`torOneScalarTower`, `torOneModule_smul`, `torOne_algebraMap_smul`,
`torOneCoefficientMap_smul`, `torOneTensorModule_smul_tmul`, and
`torOneBaseChange_tmul` state the proved canonical-action and map formulas.
`torHomology_map_smul` proves the homology scalar law needed for linearity.
The entire implementation is delivered in this same module; there are no new
holed modules or intermediate statements. Original public imports remain; the second reader removed the redundant
added public imports TensorProduct.Tower and Module.TransferInstance. Two
homology/linearity modules are added as proof-only imports.

## Users

Source-only `tools/downstream.py` finds 395 transitive importing modules.
With `--uses torOne_surjective_flat_middle` it finds only the declaration in its
own module, so no existing proof applies the changed signature. At second reading, the current
repository has no direct importer of this module: FlatOfLocalCriterionBaseChange
was replaced upstream and no longer imports it. The table below records the
transitive users at preparation time, not a fresh downstream census. Every importer
is listed below, including its holder at preparation time. No forced adaptation
is necessary: the unchanged direct importer was compiled against the repair.
Challenge.lean and all five target signatures and definitions stay unchanged;
the repaired intermediate theorem is used only through proof dependencies, not
in any target signature. The mathematical DAG statement stays byte-for-byte
unchanged. The unit's realized route stays unchanged.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.TorOneSurjectiveFlatMiddle | R1 | Repaired canonical interface and constructed data; main proof still sorry. |
| Sheaf.AlgebraicGeometry.AffineBoundaryUnitDivisorDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedEtaleNeighborhoodComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineClosedInjectiveAcyclic | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineFlatModuleDescent | T4 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineGaloisBaseChangeFiberTransitivity | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.AffineUnitDivisorBaseChangeCore | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ArbitraryRingTorsionSheafBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeClosedCoefficientRange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeOpenInjectiveCoefficientZero | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceImageLimitDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeSourceTransitionThickening | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransition | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeStalkTransportComp | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetLimitZeroDetection | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetSheafComparisonNaturality | G1 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkHigherImageComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetStalkRestrictionImage | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionComp | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionThickening | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BoundaryDivisorPicKernel | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAbelianClosedEffacement | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ComponentsFiniteSeparableDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ConstructibleModuleClosedEffacement | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffineKummerDegreeOneBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AffinePicardTorsionBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.AlgebraicallyClosedCohomologyInvariant | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierCohomologyEpi | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ArtinSchreierDimension | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryDivisorKernelPowers | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.BoundaryPointClassBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantInvariance | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantKummerNaturality | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantLowDegreeBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantModCharPDegreeTwo | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstantProperDegreeCoordinates | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeDevissage | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ConstructibleShortExactAssertions | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenAssertions | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenClosedTerm | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenCohomologyFiniteness | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomologyHigh | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenIntegralCohomologyFiniteness | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenLowBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimaryFiniteness | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.DivisorRestrictionPicard | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransfer | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.FiniteSupportPrimeGlobalSections | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecond | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericFiniteSecondReduction | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericPrimeFiltrationStep | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.GenericVanishingKernelColimit | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenCurveGmDirectImageCohomology | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.OpenLowerShriekConstantFiltrationSteps | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineBaseChangeCompatibility | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicBoundaryBaseChangeTransport | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionCoker | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionDiv | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicProperNTorsionTorsion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundary | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionBoundaryTrivial | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionDivisorCorrection | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionExact | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicRestrictionPointLift | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroJacobianPointComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicZeroTorsionBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PicardDecomposition | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.PrincipalDivisorOpenExtension | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperCohomology | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperConstantBaseChangeHigher | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperKummerDegreeOneBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ProperPicTorsionBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekAssertions | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.ReducedConstantLowerShriekReduction | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.SmoothConstantLowerShriekLocalization | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Curve.UnitsQuotientBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.DivisorClassCurve | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.DivisorPicRepresentative | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAtFieldExtension | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleFaithfullyFlatLocal | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FilteredCartesianFlatComplexDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteCoverKillsConstantCohomology | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteEtaleRestrictionFullyFaithful | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteFieldClosedComponentDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteFlatProperSupportDescent | W4 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FinitePushforwardConstantClosedEffacement | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent | S2 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FlatModuleDescent | C2 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | J2 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberConstantH1Vanishing | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberFiniteConstantTorsorsTrivial | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GabberQuotientPrincipalH1 | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeFiberTransitivity | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GaloisFiniteInvariantClopenPartition | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenericComponentsSplit | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenericFibreIncidenceSpread | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenericGeometricallyConnectedSpread | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibres | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenericPointedClopenFibresCore | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenusInvariant | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianComparisonStep | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianBoundedAbelianSurjectivity | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianClopenRestriction | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardMorphism | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HilbertToPicardSurjective | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.HomEtaleLocusTranslation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalZero | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricFibreSections | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.IntegralGeometricPointExchange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.IntegralHenselianClosedFibreSections | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.IsProperOrIsAffine | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.JacobianBaseChangeCompatible | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NoetherianSpreadingData | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalFamilyGenericLimit | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.NormalPointedFamilyApproximation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.PointedSmoothFamilyStage | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.NoetherianApproximationData | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PerfectCohomologyFromGeometric | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PerfectDiagonalDualizingEvaluation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardCupProductCriterionAux | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardDiagonalLocallyClosed | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardDirectImageRankLocus | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardEvaluationOpenLocus | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardFiberDirectImageRankConstructible | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardFunctorAgreesSC | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | V3 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosed | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuationTriviality | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardLocusClosedValuativeFactorization | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardPullbackEvaluation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardRankMatchBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardRankMatchDerivedTruncationData | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization | S2 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchFixedRankRetrocompact | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocus | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationCore | X2 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusFinitePresentationIso | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusLocallyFinitePresentation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchLocusQuasiCompact | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PicardUniversalRankMatchResidueCriterion | Q4 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineGeometricStalkReduction | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveLineStrictLocalModelComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProjectiveSpaceBaseChangeReduction | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeCompositionStability | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperBaseChangeTargetLocality | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatAffineBaseChangeHomBijective | V1 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatDerivedDirectImagePerfect | S1 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSections | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointAffineBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeChart | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointBaseChangeGlobal | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointChartMateComparison | P4 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointDirectSums | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport | T4 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatRightAdjointRestrictionOpen | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalkSurjective | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperStrictLocalFibreSections | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportLocalNoetherianModel | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericClopen | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentGenericDichotomy | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SectionComponentLocallyConstructible | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothCurveUpperShriekDifferentials | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperCurveDualizing | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperDualizingTensorEvaluation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothProperRelativeDualizing | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothSectionComponentOpen | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SteinFactorizationAffine | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselianIntegralSectionsInjective | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAbelianBaseChangeCancellation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionAssembly | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.TorsionFilteredUnion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationGenericTrivializingGenerator | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentHigherDirectImages | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ValuationProperCoherentSections | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteMonodromyTrivializingTorsor | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.ConstructibleSheaf.FiniteSetMonodromyTorsor | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverAssociatedSheaf | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.ConstructibleSheaf.SylowCoverStalkData | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.Paper.GaloisLisseRepresentations | H1 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.Paper.IntegralCoverTrivialCohomology | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.Paper.OpenCurveEtaleLerayLowDegree | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.Paper.ZariskiH0ProperHenselianPair | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.RingTheory.ColimitEventuallyFlat | A2 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.RingTheory.FlatOfFlatClosedFiber | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.RingTheory.FlatOfLocalCriterionBaseChange | Q1 | Unchanged direct proof importer; no theorem application; compiles against repaired module. |
| Sheaf.RingTheory.IsEtaleAtFieldExtensionDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.RingTheory.NoetherianFlatClosedFiberModel | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| Sheaf.RingTheory.OpenFlatLocus | T3 | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| TargetsCheck | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Cube | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Final | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.GeometricPoints | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Jacobian | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Affine | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.CohomologicalDimension | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Compactification | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Estimate | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.FieldExtension | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.GenericComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Picard | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SerreDuality | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteLocallyConstant | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.KummerTorsor | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Torsor | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorPullback | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Hilbert.Curve | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorCohomology | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorSpreading | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.Slicing | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Morphisms.SlicingFlat | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Jacobian | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.Scheme | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.AlgebraicGeometry.TheoremOfCube | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.ConstructibleSheaf.LocallyConstantReduction | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Jacobian | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.BaseChange.EtaleDerived | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | ORCHESTRA | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | ORCHESTRA | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.StrictHenselian | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.UnderivedExchange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Composition | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.CupProductWeil | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Exchange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCoherence | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalism | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekFormalismComparison | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionShift | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RefinementLowerShriekProjection | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Supports | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.TensorHom | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Gabber | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Detection | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Survival | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.IntegralBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Locality | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Vanishing | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.Integral.BaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.ClosedImmersionUpperShriek | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.Perfect | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Transitive import only; no application of changed theorem; signature and definitions unchanged. |

## Status

landed 20261013T100110-L-2481592 2026-10-13 (merge of deliver/R1/Sheaf.RingTheory.TorOneSurjectiveFlatMiddle)
