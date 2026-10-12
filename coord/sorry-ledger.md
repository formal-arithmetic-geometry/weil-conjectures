# Sorry ledger

Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.
Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.
Progress = closed − added in the closure, with pruning reported separately.

Holes now: library **2701**, closure **2003**, in definitions **9**.

Definitions with holes (def/instance/structure field):

- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup::<anonymous:instance : (derivedIdeal I).IsHopfIdeal k>` (instance, line 403)
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup::<anonymous:instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I))>` (instance, line 411)
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie::AlgebraicGeometry.GeneralLinearGroup.toMatrixLieHom` (def, line 110)
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket::<anonymous:instance : LieAlgebra Γ(S, ⊤) (Lie G)>` (instance, line 106)
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket::<anonymous:instance : LieRing (Lie G)>` (instance, line 99)
- `WeilConjectures.RingTheory.ProEtale.ClosedLift::Algebra.ClosedLift.isFiltered_index` (instance, line 142)
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar::AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekToLowerStar` (instance, line 89)
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek::AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek` (instance, line 167)
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek::AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` (instance, line 98)

| root | library | closure |
|---|---:|---:|
| Sheaf | 2437 | 1956 |
| WeilConjectures | 264 | 47 |

| baseline | scope | closed | added | net | deleted | changed holed statements |
|---|---|---:|---:|---:|---:|---:|
| 889327369 (Queue at the start of stage 3) | library | 571 | 343 | 228 | 0 | 1 |
| 660345513 (Application of proof-dependency imports) | library | 494 | 322 | 172 | 0 | 1 |
| 660345513 (Application of proof-dependency imports) | closure | 487 | 308 | 179 | 0 | 1 |

No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.

| landing class | count |
|---|---:|
| proved | 315 |
| decomposed | 4 |
| moved | 340 |
| pruned | 17 |
| other | 3 |

Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.

| group | landings | closed | added | net | moved share |
|---|---:|---:|---:|---:|---:|
| A2 | 12 | 12 | 8 | 4 | 7/12 (58.3%) |
| A3 | 9 | 10 | 14 | -4 | 7/9 (77.8%) |
| B2 | 11 | 11 | 11 | 0 | 8/11 (72.7%) |
| B3 | 17 | 17 | 11 | 6 | 8/17 (47.1%) |
| C1 | 22 | 25 | 22 | 3 | 14/22 (63.6%) |
| C2 | 13 | 13 | 11 | 2 | 7/13 (53.8%) |
| D2 | 14 | 17 | 10 | 7 | 8/14 (57.1%) |
| E1 | 27 | 35 | 19 | 16 | 14/27 (51.9%) |
| E2 | 14 | 13 | 12 | 1 | 8/14 (57.1%) |
| F1 | 23 | 26 | 21 | 5 | 12/23 (52.2%) |
| F2 | 13 | 17 | 8 | 9 | 6/13 (46.2%) |
| G1 | 20 | 23 | 19 | 4 | 11/20 (55.0%) |
| G2 | 14 | 17 | 19 | -2 | 10/14 (71.4%) |
| H1 | 17 | 18 | 10 | 8 | 6/17 (35.3%) |
| H2 | 14 | 16 | 12 | 4 | 9/14 (64.3%) |
| J1 | 21 | 27 | 13 | 14 | 10/21 (47.6%) |
| J2 | 15 | 16 | 17 | -1 | 10/15 (66.7%) |
| K1 | 20 | 24 | 21 | 3 | 12/20 (60.0%) |
| K2 | 17 | 19 | 17 | 2 | 12/17 (70.6%) |
| M1 | 19 | 24 | 13 | 11 | 8/19 (42.1%) |
| M2 | 15 | 21 | 10 | 11 | 6/15 (40.0%) |
| N1 | 22 | 23 | 20 | 3 | 13/22 (59.1%) |
| N2 | 12 | 12 | 4 | 8 | 3/12 (25.0%) |
| P1 | 23 | 40 | 21 | 19 | 13/23 (56.5%) |
| P2 | 19 | 20 | 14 | 6 | 5/19 (26.3%) |
| Q1 | 18 | 20 | 12 | 8 | 9/18 (50.0%) |
| Q2 | 13 | 13 | 6 | 7 | 4/13 (30.8%) |
| R1 | 22 | 32 | 17 | 15 | 10/22 (45.5%) |
| R2 | 13 | 14 | 8 | 6 | 5/13 (38.5%) |
| S1 | 18 | 22 | 18 | 4 | 10/18 (55.6%) |
| S2 | 16 | 17 | 15 | 2 | 9/16 (56.2%) |
| T1 | 21 | 22 | 18 | 4 | 10/21 (47.6%) |
| T2 | 15 | 21 | 7 | 14 | 5/15 (33.3%) |
| U1 | 23 | 29 | 21 | 8 | 13/23 (56.5%) |
| U2 | 17 | 17 | 12 | 5 | 8/17 (47.1%) |
| V1 | 21 | 20 | 8 | 12 | 7/21 (33.3%) |
| V2 | 14 | 15 | 8 | 7 | 5/14 (35.7%) |
| W2 | 17 | 19 | 8 | 11 | 6/17 (35.3%) |
| X2 | 13 | 13 | 13 | 0 | 7/13 (53.8%) |
| Y2 | 14 | 15 | 8 | 7 | 5/14 (35.7%) |
| Z2 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |

Nearest targets (claims from the scanned git tree; live leases may differ):

| module | distance | holes | group |
|---|---:|---:|---|
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | 0 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | 0 | 1 | ORCHESTRA |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | 1 | 1 | A2 |
| Sheaf.AlgebraicGeometry.ConstantPullbackCompositionCoherence | 2 | 1 | C1 |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | 2 | 1 | D2 |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | 2 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.Gabber | 2 | 2 | S2 |
| Sheaf.AlgebraicGeometry.Curve.ConstructiblePrimeFieldFiltration | 3 | 1 | D2 |
| Sheaf.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit | 3 | 1 | D2 |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | 3 | 1 | ORCHESTRA |
| Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension | 3 | 1 | ORCHESTRA |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | 3 | 1 | ORCHESTRA |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | 3 | 4 | — |
| Sheaf.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity | 4 | 1 | H1 |
| Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechNaturality | 4 | 1 | D2 |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | 4 | 1 | G2 |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenFinitenessComparison | 4 | 1 | H2 |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | 4 | 1 | N2 |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenVanishingComparison | 4 | 1 | P2 |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | 4 | 1 | U1 |

Modules pruned since the imports baseline:

- `Sheaf.Algebra.CharpolyLocallyFree`
- `Sheaf.Algebra.Homology.AcyclicLimitOrdinal`
- `Sheaf.Algebra.Homology.FunctorialHomotopies`
- `Sheaf.Algebra.Homology.MittagLefflerLimitHomology`
- `Sheaf.Algebra.LocallyFreeCharpoly`
- `Sheaf.Algebra.LocallyFreeCharpolyProdMap`
- `Sheaf.Algebra.Module.ProjDegreeZeroLocalizationExact`
- `Sheaf.AlgebraicGeometry.AffineFibreProductTransition`
- `Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`
- `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric`
- `Sheaf.AlgebraicGeometry.DescendQCOpenFGSubalgebra`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `Sheaf.AlgebraicGeometry.FibreProductLimit`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `Sheaf.AlgebraicGeometry.FiniteAffineFibreSections`
- `Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`
- `Sheaf.AlgebraicGeometry.FirstOrderThickeningBaseChange`
- `Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections`
- `Sheaf.AlgebraicGeometry.FlatModulePullbackExact`
- `Sheaf.AlgebraicGeometry.FlatUnramifiedFormallyEtale`
- `Sheaf.AlgebraicGeometry.FormalFibreCohomology`
- `Sheaf.AlgebraicGeometry.FormalFunctionsStalk`
- `Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal`
- `Sheaf.AlgebraicGeometry.FpqcAffineDescent`
- `Sheaf.AlgebraicGeometry.FpqcAffineStandardRefinement`
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`
- `Sheaf.AlgebraicGeometry.FpqcTensorSections`
- `Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends`
- `Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends`
- `Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection`
- `Sheaf.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension`
- `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion`
- `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest`
- `Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting`
- `Sheaf.AlgebraicGeometry.HypercoverOneMoreSimplex`
- `Sheaf.AlgebraicGeometry.LimitFibreProducts`
- `Sheaf.AlgebraicGeometry.LimitResidueField`
- `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty`
- `Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent`
- `Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents`
- `Sheaf.AlgebraicGeometry.NormalizationProperties`
- `Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage`
- `Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange`
- `Sheaf.AlgebraicGeometry.ProperNormalizedFibres`
- `Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember`
- `Sheaf.AlgebraicGeometry.SemiRepresentableCoveringPermanence`
- `Sheaf.AlgebraicGeometry.SemiRepresentableObject`
- `Sheaf.AlgebraicGeometry.SimplicialHomObject`
- `Sheaf.AlgebraicGeometry.SimplicialHomObjectExists`
- `Sheaf.AlgebraicGeometry.SimplicialHomObjectPushout`
- `Sheaf.AlgebraicGeometry.SimplicialHomStandardSimplex`
- `Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`
- `Sheaf.AlgebraicGeometry.StandardFpqcQuotientTopology`
- `Sheaf.AlgebraicGeometry.SteinFactorizationAffine`
- `Sheaf.AlgebraicGeometry.SteinUniversallyClosedFactor`
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists`
- `Sheaf.AlgebraicGeometry.UniversalThickeningAffineCase`
- `Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange`
- `Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces`
- `Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestriction`
- `Sheaf.AlgebraicGeometry.UpperShriekRightAdjoint`
- `Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`
- `Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan`
- `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`
- `Sheaf.AlgebraicTopology.GlueSimplex`
- `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution`
- `Sheaf.AlgebraicTopology.SimplicialIndexFiniteInitial`
- `Sheaf.CategoryTheory.Abelian.CompatibleNullHomotopyAssembly`
- `Sheaf.CategoryTheory.BoundedSubobjectSize`
- `Sheaf.CategoryTheory.BoundedSubobjectSurjection`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence`
- `Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy`
- `Sheaf.CategoryTheory.CartanEilenbergVerticalNullhomotopy`
- `Sheaf.CategoryTheory.ColimitSiteCechComplex`
- `Sheaf.CategoryTheory.CoskeletonMatchingTuples`
- `Sheaf.CategoryTheory.EssentiallyConstantSplitting`
- `Sheaf.CategoryTheory.EssentiallyConstantSystem`
- `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence`
- `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`
- `Sheaf.CategoryTheory.Galois.GaloisTransitive`
- `Sheaf.CategoryTheory.Galois.StacksGaloisObjectExists`
- `Sheaf.CategoryTheory.GrothendieckAbelian.AcyclicQuotientComplexesBoundedSize`
- `Sheaf.CategoryTheory.GrothendieckAbelian.FunctorialInjectiveComplexEmbedding`
- `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveCriterion`
- `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveDegreewiseExistence`
- `Sheaf.CategoryTheory.GrothendieckAbelian.ObjectsSmall`
- `Sheaf.CategoryTheory.HomotopyHomExactOfInjective`
- `Sheaf.CategoryTheory.HomotopyLimitVanishing`
- `Sheaf.CategoryTheory.HorizontalComparisonLift`
- `Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator`
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`
- `Sheaf.CategoryTheory.MittagLefflerExactSequence`
- `Sheaf.CategoryTheory.MittagLefflerLimitExact`
- `Sheaf.CategoryTheory.ProperFaceMatchingObject`
- `Sheaf.CategoryTheory.SimplicialMatchingObject`
- `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement`
- `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`
- `Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf`
- `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`
- `Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants`
- `Sheaf.Paper.CechNerveFreeHomology`
- `Sheaf.Paper.ColimitSitesInjectiveSystem`
- `Sheaf.Paper.ColimitSurjectiveRingMap`
- `Sheaf.Paper.ConstantSheafOpenMaps`
- `Sheaf.Paper.EtaleHypercover`
- `Sheaf.Paper.EtaleHypercoverProduct`
- `Sheaf.Paper.FiniteHypercoverDescent`
- `Sheaf.Paper.FiniteSplitEtaleHypercover`
- `Sheaf.Paper.FiniteSplitHypercoverRefinement`
- `Sheaf.Paper.HypercoverCohomology`
- `Sheaf.Paper.HypercoverCohomologyColimit`
- `Sheaf.Paper.HypercoverFreeResolution`
- `Sheaf.Paper.ImagePresheafSheafificationIso`
- `Sheaf.Paper.InverseImageExtensionByEmptyConstant`
- `Sheaf.Paper.InverseImageFreeEtaleModule`
- `Sheaf.Paper.PlusConstructionFunctorial`
- `Sheaf.Paper.SheavesKilledByNZmodModules`
- `Sheaf.Paper.SimplicialSetAddSimplices`
- `Sheaf.Paper.SiteCoveringMorphismsSameH0Map`
- `Sheaf.Paper.SitePlusInjectiveSeparated`
- `Sheaf.Paper.SitePlusOfSeparatedIsSheaf`
- `Sheaf.Paper.SitePlusOfSheafIso`
- `Sheaf.Paper.SitePlusSeparated`
- `Sheaf.Paper.TrivialKanHomotopyEquivalence`
- `Sheaf.Paper.ZariskiH0ProperHenselianPair`
- `Sheaf.RingTheory.FlatModuleCompletion`
- `Sheaf.RingTheory.HenselianPairPrimeConnected`
- `Sheaf.RingTheory.LimitFlatModules`
- `Sheaf.RingTheory.MapIntoHenselianColimit`
- `Sheaf.RingTheory.TorStrictlyProZero`
- `Sheaf.RingTheory.UniversalFirstOrderThickening`
- `Sheaf.Topology.ClosedPushforwardConstantPresheaf`
- `Sheaf.Topology.ClosedPushforwardConstantRestriction`
- `Sheaf.Topology.ClosedPushforwardConstantStalks`
- `Sheaf.Topology.ExistsUniqueIsGenericPointOfFinite`
- `Sheaf.Topology.InverseImageClosedPushforwardConstant`
- `Sheaf.Topology.LocallyConstantGermEvaluation`
- `Sheaf.Topology.SetsExtensionByEmpty`
- `Sheaf.Topology.SetsExtensionByEmptyAdjunction`
- `Sheaf.Topology.SetsInverseImageComposition`
- `Sheaf.Topology.SheafBasisSurjection`
- `Sheaf.Topology.SheafDirectedColimitFiniteCoequalizers`
- `Sheaf.Topology.SheafFiniteRelationTruncations`
- `Sheaf.Topology.SheafFiniteTruncationColimit`
- `Sheaf.Topology.SheavesInjectiveDirectedColimitSections`
- `Sheaf.Topology.SkyscraperConstantOnPointClosure`
- `Sheaf.Topology.Spectral.ConstructibleTopologyHausdorff`
- `Sheaf.Topology.SpectralClosedSubspace`
- `Sheaf.Topology.SpectralDirectedLimit`
- `Sheaf.Topology.SpectralDirectedLimitFiniteSober`
- `Sheaf.Topology.SpectralFiniteCoequalizer`
- `Sheaf.Topology.SpectralFiniteCoequalizerEmbedsConstant`
- `Sheaf.Topology.SpectralLimitConstructibleClosed`
- `Sheaf.Topology.SpectralLimitConstructibleClosedNonempty`
- `Sheaf.Topology.SpectralLimitDescendOpens`
- `Sheaf.Topology.SpectralLimitPullbackSections`
- `Sheaf.Topology.SpectralMapConstructibleContinuous`
- `Sheaf.Topology.SpectralSheafColimitConstantEmbeddings`
- `Sheaf.Topology.SurjectionKernelPairCoequalizer`
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement`
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.FiniteBound`
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.FinitePresentation`
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GeometricLifts`
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.Induction`
- `WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.Specialization`
- `WeilConjectures.Mathlib.FieldTheory.Fixed`

Scanner limitations: macro-generated declarations, elaborated anonymous/private names, and tactic dependencies cannot be recovered from source. Synthetic names are source keys, not elaborated names.

Diagnostics:

- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup: anonymous holed declaration: <anonymous:instance : (derivedIdeal I).IsHopfIdeal k>
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup: anonymous holed declaration: <anonymous:instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I))>
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket: anonymous holed declaration: <anonymous:instance : LieAlgebra Γ(S, ⊤) (Lie G)>
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket: anonymous holed declaration: <anonymous:instance : LieRing (Lie G)>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderRetracts>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ>
