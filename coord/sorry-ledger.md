# Sorry ledger

Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.
Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.
Progress = closed − added in the closure, with pruning reported separately.

Holes now: library **2656**, closure **1910**, holes in definitions **9**, definitions with undetermined data **10** (closure **8**).

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

Definitions with undetermined data (class-1 exceptions in `coord/hollow-definitions.md`):

- `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap::AlgebraicGeometry.affineDerivedExtensionAdjunction` (line 117), chosen from `AlgebraicGeometry.exists_affineDerivedExtension`
- `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap::AlgebraicGeometry.canonicalPullbackAdjunction` (line 127), chosen from `AlgebraicGeometry.exists_derivedPullbackComposition`, `AlgebraicGeometry.exists_schemeDerivedAdjunction`
- `Sheaf.AlgebraicGeometry.DualityEquationBaseChangeMap::AlgebraicGeometry.dualityEquationBaseChangeMap` (line 49), chosen from `AlgebraicGeometry.exists_derivedPullbackComposition`, `AlgebraicGeometry.exists_schemeDerivedAdjunction`
- `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso::AlgebraicGeometry.schemeHomPullbackAdjunction` (line 105), chosen from `AlgebraicGeometry.exists_derivedPullbackComposition`, `AlgebraicGeometry.exists_schemeDerivedAdjunction`
- `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso::AlgebraicGeometry.schemeHomTensorPullbackIso` (line 128), chosen from `AlgebraicGeometry.exists_schemeHomTensorPullbackIso`
- `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms::AlgebraicGeometry.perfectDescentComparison` (line 44), chosen from `AlgebraicGeometry.exists_derivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap::AlgebraicGeometry.schemeDerivedBaseChangeMap` (line 89), chosen from `AlgebraicGeometry.exists_derivedPullbackComposition`, `AlgebraicGeometry.exists_schemeDerivedAdjunction`
- `Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition::AlgebraicGeometry.SingleComplexBaseChange.counit` (line 46), chosen from `AlgebraicGeometry.exists_derivedPullbackComposition`
- `Sheaf.Paper.LisseAdicFiberFunctors::AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor` (line 144), chosen from `AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor_exists`
- `Sheaf.Paper.LisseAdicSheaves::AlgebraicGeometry.Scheme.lisseCoefficientDiagramData` (line 527), chosen from `AlgebraicGeometry.Scheme.lisseCoefficientDiagram_exists`

| root | library | closure |
|---|---:|---:|
| Sheaf | 2392 | 1863 |
| WeilConjectures | 264 | 47 |

| baseline | scope | closed | added | net | deleted | changed holed statements |
|---|---|---:|---:|---:|---:|---:|
| 889327369 (Queue at the start of stage 3) | library | 617 | 344 | 273 | 0 | 1 |
| 660345513 (Application of proof-dependency imports) | library | 541 | 324 | 217 | 0 | 1 |
| 660345513 (Application of proof-dependency imports) | closure | 534 | 310 | 224 | 0 | 1 |

No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.

| landing class | count |
|---|---:|
| proved | 383 |
| decomposed | 4 |
| moved | 396 |
| pruned | 20 |
| other | 3 |

Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.

| group | landings | closed | added | net | moved share |
|---|---:|---:|---:|---:|---:|
| A2 | 15 | 15 | 9 | 6 | 8/15 (53.3%) |
| A3 | 14 | 17 | 17 | 0 | 9/14 (64.3%) |
| B2 | 14 | 14 | 14 | 0 | 10/14 (71.4%) |
| B3 | 24 | 26 | 16 | 10 | 10/24 (41.7%) |
| C1 | 28 | 32 | 27 | 5 | 18/28 (64.3%) |
| C2 | 13 | 13 | 11 | 2 | 7/13 (53.8%) |
| D2 | 17 | 20 | 12 | 8 | 10/17 (58.8%) |
| E1 | 31 | 39 | 19 | 20 | 14/31 (45.2%) |
| E2 | 19 | 18 | 17 | 1 | 11/19 (57.9%) |
| F1 | 25 | 28 | 21 | 7 | 12/25 (48.0%) |
| F2 | 16 | 20 | 11 | 9 | 8/16 (50.0%) |
| G1 | 22 | 25 | 19 | 6 | 11/22 (50.0%) |
| G2 | 15 | 18 | 19 | -1 | 10/15 (66.7%) |
| H1 | 20 | 21 | 12 | 9 | 8/20 (40.0%) |
| H2 | 16 | 18 | 13 | 5 | 10/16 (62.5%) |
| J1 | 26 | 33 | 16 | 17 | 12/26 (46.2%) |
| J2 | 16 | 17 | 18 | -1 | 11/16 (68.8%) |
| K1 | 24 | 28 | 23 | 5 | 14/24 (58.3%) |
| K2 | 21 | 23 | 19 | 4 | 14/21 (66.7%) |
| M1 | 23 | 28 | 15 | 13 | 9/23 (39.1%) |
| M2 | 17 | 23 | 12 | 11 | 7/17 (41.2%) |
| N1 | 23 | 24 | 20 | 4 | 13/23 (56.5%) |
| N2 | 14 | 14 | 5 | 9 | 4/14 (28.6%) |
| P1 | 27 | 44 | 23 | 21 | 15/27 (55.6%) |
| P2 | 24 | 25 | 14 | 11 | 5/24 (20.8%) |
| Q1 | 20 | 22 | 16 | 6 | 11/20 (55.0%) |
| Q2 | 13 | 13 | 6 | 7 | 4/13 (30.8%) |
| R1 | 25 | 35 | 18 | 17 | 11/25 (44.0%) |
| R2 | 17 | 18 | 12 | 6 | 8/17 (47.1%) |
| S1 | 21 | 25 | 21 | 4 | 12/21 (57.1%) |
| S2 | 19 | 20 | 17 | 3 | 10/19 (52.6%) |
| T1 | 24 | 25 | 20 | 5 | 11/24 (45.8%) |
| T2 | 20 | 26 | 12 | 14 | 7/20 (35.0%) |
| U1 | 26 | 32 | 23 | 9 | 15/26 (57.7%) |
| U2 | 21 | 21 | 15 | 6 | 10/21 (47.6%) |
| V1 | 24 | 23 | 12 | 11 | 9/24 (37.5%) |
| V2 | 18 | 19 | 14 | 5 | 8/18 (44.4%) |
| W2 | 18 | 20 | 8 | 12 | 6/18 (33.3%) |
| X2 | 18 | 18 | 16 | 2 | 8/18 (44.4%) |
| Y2 | 17 | 19 | 10 | 9 | 6/17 (35.3%) |
| Z2 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |

Nearest targets (claims from the scanned git tree; live leases may differ):

| module | distance | holes | group |
|---|---:|---:|---|
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | 0 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | 0 | 1 | ORCHESTRA |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | 1 | 1 | A2 |
| Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties | 2 | 1 | D2 |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | 2 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.Gabber | 2 | 2 | S2 |
| Sheaf.AlgebraicGeometry.Curve.EtaleSheafHLargeFilteredColimit | 3 | 1 | D2 |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | 3 | 1 | ORCHESTRA |
| Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension | 3 | 1 | ORCHESTRA |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | 3 | 1 | ORCHESTRA |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | 3 | 4 | — |
| Sheaf.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity | 4 | 1 | H1 |
| Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechNaturality | 4 | 1 | D2 |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenBaseChangeComparison | 4 | 1 | G2 |
| Sheaf.AlgebraicGeometry.Curve.DenseOpenRestrictionComparison | 4 | 1 | N2 |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | 4 | 1 | V1 |
| Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientConstructibilityTransfer | 4 | 1 | U2 |
| Sheaf.AlgebraicGeometry.DerivedExchangeBoundedComparison | 4 | 1 | P1 |
| Sheaf.AlgebraicGeometry.EtaleConstantRingInverseImageComparison | 4 | 1 | F1 |
| Sheaf.AlgebraicGeometry.EtaleModuleInverseImageTransport | 4 | 1 | F1 |

Modules pruned since the imports baseline:

- `Sheaf.Algebra.Category.ModuleCat.RingScalarExtension`
- `Sheaf.Algebra.CharpolyLocallyFree`
- `Sheaf.Algebra.Homology.AcyclicLimitOrdinal`
- `Sheaf.Algebra.Homology.FunctorialHomotopies`
- `Sheaf.Algebra.Homology.MappingCylinderSplitFactorization`
- `Sheaf.Algebra.Homology.MittagLefflerLimitHomology`
- `Sheaf.Algebra.Homology.UpperTruncationStepSES`
- `Sheaf.Algebra.LocallyFreeCharpoly`
- `Sheaf.Algebra.LocallyFreeCharpolyProdMap`
- `Sheaf.Algebra.Module.ProjDegreeZeroLocalizationExact`
- `Sheaf.AlgebraicGeometry.AffineFibreProductTransition`
- `Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`
- `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.DescendQCOpenFGSubalgebra`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `Sheaf.AlgebraicGeometry.FibreProductLimit`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `Sheaf.AlgebraicGeometry.FiniteAffineFibreSections`
- `Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`
- `Sheaf.AlgebraicGeometry.FiniteSeparableMultiplicationEtale`
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
- `Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing`
- `Sheaf.AlgebraicGeometry.SemiRepresentableCoveringPermanence`
- `Sheaf.AlgebraicGeometry.SemiRepresentableObject`
- `Sheaf.AlgebraicGeometry.SimplicialHomObject`
- `Sheaf.AlgebraicGeometry.SimplicialHomObjectExists`
- `Sheaf.AlgebraicGeometry.SimplicialHomObjectPushout`
- `Sheaf.AlgebraicGeometry.SimplicialHomStandardSimplex`
- `Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`
- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`
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
- `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroExact`
- `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`
- `Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan`
- `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`
- `Sheaf.AlgebraicTopology.GlueSimplex`
- `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution`
- `Sheaf.AlgebraicTopology.SimplicialIndexFiniteInitial`
- `Sheaf.CategoryTheory.BoundedSubobjectSize`
- `Sheaf.CategoryTheory.BoundedSubobjectSurjection`
- `Sheaf.CategoryTheory.CoskeletonMatchingTuples`
- `Sheaf.CategoryTheory.EdgeCollapse`
- `Sheaf.CategoryTheory.EssentiallyConstantSplitting`
- `Sheaf.CategoryTheory.EssentiallyConstantSystem`
- `Sheaf.CategoryTheory.Galois.GaloisTransitive`
- `Sheaf.CategoryTheory.Galois.StacksGaloisObjectExists`
- `Sheaf.CategoryTheory.GrothendieckAbelian.AcyclicQuotientComplexesBoundedSize`
- `Sheaf.CategoryTheory.GrothendieckAbelian.FunctorialInjectiveComplexEmbedding`
- `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveCriterion`
- `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveDegreewiseExistence`
- `Sheaf.CategoryTheory.GrothendieckAbelian.ObjectsSmall`
- `Sheaf.CategoryTheory.HomotopyHomExactOfInjective`
- `Sheaf.CategoryTheory.HomotopyLimitVanishing`
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
- `Sheaf.CategoryTheory.TruncationCoupleExact`
- `Sheaf.CategoryTheory.TruncationDescends`
- `Sheaf.CategoryTheory.TruncationTriangle`
- `Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants`
- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`
- `Sheaf.NumberTheory.Padics.CoefficientExtension`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`
- `Sheaf.NumberTheory.Padics.LatticeStabilizerOpen`
- `Sheaf.Paper.AdicTowerReconstruction`
- `Sheaf.Paper.CechNerveFreeHomology`
- `Sheaf.Paper.ColimitSurjectiveRingMap`
- `Sheaf.Paper.ConstantSheafOpenMaps`
- `Sheaf.Paper.EtaleHypercover`
- `Sheaf.Paper.EtaleHypercoverProduct`
- `Sheaf.Paper.FiniteHypercoverDescent`
- `Sheaf.Paper.FiniteSplitEtaleHypercover`
- `Sheaf.Paper.FiniteSplitHypercoverRefinement`
- `Sheaf.Paper.GaloisLisseRepresentations`
- `Sheaf.Paper.HypercoverCohomology`
- `Sheaf.Paper.HypercoverCohomologyColimit`
- `Sheaf.Paper.HypercoverFreeResolution`
- `Sheaf.Paper.ImagePresheafSheafificationIso`
- `Sheaf.Paper.InverseImageExtensionByEmptyConstant`
- `Sheaf.Paper.InverseImageFreeEtaleModule`
- `Sheaf.Paper.LisseAdicFiberFunctors`
- `Sheaf.Paper.LisseAdicSheaves`
- `Sheaf.Paper.LisseTensorScalarExtension`
- `Sheaf.Paper.PlusConstructionFunctorial`
- `Sheaf.Paper.SimplicialSetAddSimplices`
- `Sheaf.Paper.SiteCoveringMorphismsSameH0Map`
- `Sheaf.Paper.SitePlusInjectiveSeparated`
- `Sheaf.Paper.SitePlusOfSeparatedIsSheaf`
- `Sheaf.Paper.SitePlusOfSheafIso`
- `Sheaf.Paper.SitePlusSeparated`
- `Sheaf.Paper.TrivialKanHomotopyEquivalence`
- `Sheaf.Paper.ZariskiH0ProperHenselianPair`
- `Sheaf.RepresentationTheory.LAdic`
- `Sheaf.RepresentationTheory.ProfiniteStableLattice`
- `Sheaf.RingTheory.FlatModuleCompletion`
- `Sheaf.RingTheory.HenselianPairPrimeConnected`
- `Sheaf.RingTheory.LimitFlatModules`
- `Sheaf.RingTheory.MapIntoHenselianColimit`
- `Sheaf.RingTheory.TorStrictlyProZero`
- `Sheaf.RingTheory.UniversalFirstOrderThickening`
- `Sheaf.Topology.ClosedPushforwardConstantRestriction`
- `Sheaf.Topology.ExistsUniqueIsGenericPointOfFinite`
- `Sheaf.Topology.InverseImageClosedPushforwardConstant`
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
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorSequence`

Scanner limitations: macro-generated declarations, elaborated anonymous/private names, and tactic dependencies cannot be recovered from source. Synthetic names are source keys, not elaborated names.

Diagnostics:

- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup: anonymous holed declaration: <anonymous:instance : (derivedIdeal I).IsHopfIdeal k>
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup: anonymous holed declaration: <anonymous:instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I))>
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket: anonymous holed declaration: <anonymous:instance : LieAlgebra Γ(S, ⊤) (Lie G)>
- WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket: anonymous holed declaration: <anonymous:instance : LieRing (Lie G)>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderRetracts>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ>
