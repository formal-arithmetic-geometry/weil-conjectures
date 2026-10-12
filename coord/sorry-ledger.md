# Sorry ledger

Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.
Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.
Progress = closed − added in the closure, with pruning reported separately.

Holes now: library **2345**, closure **1556**, holes in definitions **9**, definitions with undetermined data **4** (closure **2**).

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

- `Sheaf.AlgebraicGeometry.AffineGlobalHomBaseChangeMap::AlgebraicGeometry.affineDerivedExtensionAdjunction` (line 119), chosen from `AlgebraicGeometry.exists_affineDerivedExtension`
- `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso::AlgebraicGeometry.schemeHomTensorPullbackIso` (line 128), chosen from `AlgebraicGeometry.exists_schemeHomTensorPullbackIso`
- `Sheaf.Paper.LisseAdicFiberFunctors::AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor` (line 144), chosen from `AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor_exists`
- `Sheaf.Paper.LisseAdicSheaves::AlgebraicGeometry.Scheme.lisseCoefficientDiagramData` (line 527), chosen from `AlgebraicGeometry.Scheme.lisseCoefficientDiagram_exists`

| root | library | closure |
|---|---:|---:|
| Sheaf | 2087 | 1515 |
| WeilConjectures | 258 | 41 |

| baseline | scope | closed | added | net | deleted | changed holed statements |
|---|---|---:|---:|---:|---:|---:|
| 889327369 (Queue at the start of stage 3) | library | 1059 | 475 | 584 | 0 | 1 |
| 660345513 (Application of proof-dependency imports) | library | 984 | 456 | 528 | 0 | 1 |
| 660345513 (Application of proof-dependency imports) | closure | 965 | 433 | 532 | 0 | 1 |

No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.

| landing class | count |
|---|---:|
| proved | 825 |
| decomposed | 8 |
| moved | 837 |
| pruned | 38 |
| other | 7 |

Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.

| group | landings | closed | added | net | moved share |
|---|---:|---:|---:|---:|---:|
| A2 | 32 | 31 | 25 | 6 | 19/32 (59.4%) |
| A3 | 31 | 34 | 22 | 12 | 13/31 (41.9%) |
| B2 | 29 | 30 | 25 | 5 | 17/29 (58.6%) |
| B3 | 40 | 44 | 22 | 22 | 15/40 (37.5%) |
| C1 | 44 | 48 | 36 | 12 | 24/44 (54.5%) |
| C2 | 28 | 28 | 22 | 6 | 16/28 (57.1%) |
| C3 | 18 | 18 | 14 | 4 | 10/18 (55.6%) |
| D2 | 40 | 44 | 32 | 12 | 23/40 (57.5%) |
| D3 | 19 | 19 | 11 | 8 | 6/19 (31.6%) |
| E1 | 43 | 53 | 25 | 28 | 19/43 (44.2%) |
| E2 | 32 | 31 | 29 | 2 | 19/32 (59.4%) |
| E3 | 14 | 14 | 10 | 4 | 7/14 (50.0%) |
| F1 | 41 | 45 | 31 | 14 | 18/41 (43.9%) |
| F2 | 28 | 43 | 18 | 25 | 13/28 (46.4%) |
| F3 | 16 | 20 | 9 | 11 | 5/16 (31.2%) |
| G1 | 43 | 46 | 44 | 2 | 24/43 (55.8%) |
| G2 | 35 | 38 | 35 | 3 | 20/35 (57.1%) |
| G3 | 15 | 21 | 10 | 11 | 7/15 (46.7%) |
| H1 | 36 | 37 | 30 | 7 | 21/36 (58.3%) |
| H2 | 30 | 32 | 21 | 11 | 17/30 (56.7%) |
| H3 | 19 | 27 | 12 | 15 | 10/19 (52.6%) |
| J1 | 39 | 45 | 20 | 25 | 15/39 (38.5%) |
| J2 | 31 | 34 | 30 | 4 | 20/31 (64.5%) |
| J3 | 17 | 17 | 4 | 13 | 3/17 (17.6%) |
| K1 | 39 | 43 | 33 | 10 | 22/39 (56.4%) |
| K2 | 38 | 42 | 29 | 13 | 23/38 (60.5%) |
| K3 | 17 | 18 | 7 | 11 | 6/17 (35.3%) |
| M1 | 43 | 47 | 26 | 21 | 16/43 (37.2%) |
| M2 | 31 | 39 | 22 | 17 | 13/31 (41.9%) |
| M3 | 18 | 18 | 7 | 11 | 7/18 (38.9%) |
| N1 | 37 | 39 | 28 | 11 | 20/37 (54.1%) |
| N2 | 30 | 36 | 16 | 20 | 13/30 (43.3%) |
| N3 | 11 | 11 | 7 | 4 | 5/11 (45.5%) |
| P1 | 43 | 63 | 30 | 33 | 20/43 (46.5%) |
| P2 | 42 | 45 | 24 | 21 | 14/42 (33.3%) |
| P3 | 15 | 15 | 17 | -2 | 9/15 (60.0%) |
| Q1 | 30 | 32 | 20 | 12 | 14/30 (46.7%) |
| Q2 | 28 | 29 | 22 | 7 | 14/28 (50.0%) |
| Q3 | 15 | 17 | 13 | 4 | 7/15 (46.7%) |
| R1 | 43 | 53 | 32 | 21 | 20/43 (46.5%) |
| R2 | 34 | 37 | 30 | 7 | 19/34 (55.9%) |
| R3 | 13 | 16 | 6 | 10 | 4/13 (30.8%) |
| S1 | 35 | 38 | 37 | 1 | 21/35 (60.0%) |
| S2 | 33 | 35 | 29 | 6 | 17/33 (51.5%) |
| S3 | 13 | 15 | 5 | 10 | 4/13 (30.8%) |
| T1 | 39 | 40 | 32 | 8 | 21/39 (53.8%) |
| T2 | 26 | 36 | 15 | 21 | 10/26 (38.5%) |
| T3 | 13 | 13 | 15 | -2 | 8/13 (61.5%) |
| U1 | 43 | 49 | 40 | 9 | 27/43 (62.8%) |
| U2 | 35 | 35 | 23 | 12 | 15/35 (42.9%) |
| U3 | 14 | 14 | 9 | 5 | 7/14 (50.0%) |
| V1 | 38 | 37 | 18 | 19 | 14/38 (36.8%) |
| V2 | 30 | 31 | 26 | 5 | 16/30 (53.3%) |
| V3 | 18 | 22 | 9 | 13 | 7/18 (38.9%) |
| W2 | 28 | 30 | 13 | 17 | 10/28 (35.7%) |
| W3 | 20 | 20 | 13 | 7 | 9/20 (45.0%) |
| X2 | 32 | 32 | 34 | -2 | 18/32 (56.2%) |
| X3 | 7 | 8 | 4 | 4 | 2/7 (28.6%) |
| Y2 | 34 | 36 | 28 | 8 | 17/34 (50.0%) |
| Y3 | 9 | 10 | 9 | 1 | 7/9 (77.8%) |
| Z2 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |

Nearest targets (claims from the scanned git tree; live leases may differ):

| module | distance | holes | group |
|---|---:|---:|---|
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | 0 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | 0 | 1 | ORCHESTRA |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | 1 | 1 | B3 |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | 2 | 1 | E1 |
| WeilConjectures.SixFunctors.Etale.Gabber | 2 | 2 | M1 |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant | 3 | 1 | T2 |
| Sheaf.AlgebraicGeometry.Curve.NormalizationComparisonOnIsoLocus | 3 | 1 | — |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | 3 | 1 | E3 |
| Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension | 3 | 1 | G2 |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | 3 | 1 | F1 |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | 3 | 4 | — |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | 4 | 1 | R1 |
| Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres | 4 | 1 | F1 |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | 4 | 1 | G3 |
| Sheaf.FieldTheory.FieldTensorUniqueMinimalPrime | 4 | 1 | F3 |
| Sheaf.Paper.StrictHenselizationPointedMap | 4 | 2 | Y2 |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationCoreData | 5 | 1 | G3 |
| Sheaf.AlgebraicGeometry.ConstantExtensionCokernelAux | 5 | 2 | G2 |
| Sheaf.AlgebraicGeometry.Curve.LowerShriekCoefficientCounit | 5 | 1 | U2 |
| Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence | 5 | 2 | H2 |

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
- `Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`
- `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.DescendQCOpenFGSubalgebra`
- `Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `Sheaf.AlgebraicGeometry.FibreProductLimit`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `Sheaf.AlgebraicGeometry.FiniteAffineFibreSections`
- `Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen`
- `Sheaf.AlgebraicGeometry.FiniteDiscreteSeparatedAffine`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`
- `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`
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
- `Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion`
- `Sheaf.AlgebraicGeometry.FpqcTensorSections`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer`
- `Sheaf.AlgebraicGeometry.GaloisBaseChangeQCOpenDescends`
- `Sheaf.AlgebraicGeometry.GaloisInvariantClosedSubsetDescends`
- `Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection`
- `Sheaf.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension`
- `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiberEtaleCriterion`
- `Sheaf.AlgebraicGeometry.GeometricallyConnectedFiniteSeparableTest`
- `Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting`
- `Sheaf.AlgebraicGeometry.HypercoverOneMoreSimplex`
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom`
- `Sheaf.AlgebraicGeometry.LftOverFieldIsolatedPointResidueFinite`
- `Sheaf.AlgebraicGeometry.LimitFibreProducts`
- `Sheaf.AlgebraicGeometry.LimitResidueField`
- `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty`
- `Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent`
- `Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope`
- `Sheaf.AlgebraicGeometry.NagataFixedBaseSeparatedStage`
- `Sheaf.AlgebraicGeometry.NilpotentBaseChangeIdempotents`
- `Sheaf.AlgebraicGeometry.NormalizationProperties`
- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition`
- `Sheaf.AlgebraicGeometry.ProperFibreIdempotentImage`
- `Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange`
- `Sheaf.AlgebraicGeometry.ProperNormalizedFibres`
- `Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember`
- `Sheaf.AlgebraicGeometry.SchemeTheoreticUnion`
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
- `Sheaf.AlgebraicGeometry.StandardSmoothAffineDiagonalGenerators`
- `Sheaf.AlgebraicGeometry.SteinFactorizationAffine`
- `Sheaf.AlgebraicGeometry.SteinUniversallyClosedFactor`
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists`
- `Sheaf.AlgebraicGeometry.UniversalThickeningAffineCase`
- `Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange`
- `Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces`
- `Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestriction`
- `Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover`
- `Sheaf.AlgebraicGeometry.UpperShriekRightAdjoint`
- `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroExact`
- `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`
- `Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan`
- `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`
- `Sheaf.AlgebraicTopology.GlueSimplex`
- `Sheaf.AlgebraicTopology.SimplicialIndexFiniteInitial`
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
- `Sheaf.CategoryTheory.AdjunctionTransferFunctorialInjectives`
- `Sheaf.CategoryTheory.BoundedSubobjectSize`
- `Sheaf.CategoryTheory.BoundedSubobjectSurjection`
- `Sheaf.CategoryTheory.CartanEilenbergProperties`
- `Sheaf.CategoryTheory.CohomologyColimitSites`
- `Sheaf.CategoryTheory.CoskeletonMatchingTuples`
- `Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification`
- `Sheaf.CategoryTheory.DiscreteModulesAbelian`
- `Sheaf.CategoryTheory.EdgeCollapse`
- `Sheaf.CategoryTheory.EquivalenceInternalModule`
- `Sheaf.CategoryTheory.EssentiallyConstantSplitting`
- `Sheaf.CategoryTheory.EssentiallyConstantSystem`
- `Sheaf.CategoryTheory.FiniteContinuousModule`
- `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`
- `Sheaf.CategoryTheory.Galois.AbstractEquivalence`
- `Sheaf.CategoryTheory.Galois.CoproductMorphismComponents`
- `Sheaf.CategoryTheory.Galois.GaloisTransitive`
- `Sheaf.CategoryTheory.Galois.StacksGaloisAxioms`
- `Sheaf.CategoryTheory.Galois.StacksGaloisCategory`
- `Sheaf.CategoryTheory.Galois.StacksGaloisObjectExists`
- `Sheaf.CategoryTheory.GrothendieckAbelian.AcyclicQuotientComplexesBoundedSize`
- `Sheaf.CategoryTheory.GrothendieckAbelian.FunctorialInjectiveComplexEmbedding`
- `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveCriterion`
- `Sheaf.CategoryTheory.GrothendieckAbelian.KInjectiveDegreewiseExistence`
- `Sheaf.CategoryTheory.GrothendieckAbelian.ObjectsSmall`
- `Sheaf.CategoryTheory.GrothendieckSSDoubleComplexModel`
- `Sheaf.CategoryTheory.HalfPlaneGradedCanonical`
- `Sheaf.CategoryTheory.HomotopyHomExactOfInjective`
- `Sheaf.CategoryTheory.HomotopyLimitVanishing`
- `Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator`
- `Sheaf.CategoryTheory.InternalModule`
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`
- `Sheaf.CategoryTheory.MittagLefflerExactSequence`
- `Sheaf.CategoryTheory.MittagLefflerLimitExact`
- `Sheaf.CategoryTheory.ProperFaceMatchingObject`
- `Sheaf.CategoryTheory.QuotientJShriek`
- `Sheaf.CategoryTheory.SimplicialMatchingObject`
- `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorPushoutExtension`
- `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`
- `Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf`
- `Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation`
- `Sheaf.CategoryTheory.Sites.TorsorH1Functoriality`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedProductPresentation`
- `Sheaf.CategoryTheory.Sites.ZariskiTorsorExtensionPushout`
- `Sheaf.CategoryTheory.SpectralSequenceComparison`
- `Sheaf.CategoryTheory.Triangulated.TriangleMorphismExtension`
- `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`
- `Sheaf.CategoryTheory.TruncationCoupleExact`
- `Sheaf.CategoryTheory.TruncationDescends`
- `Sheaf.CategoryTheory.TruncationTriangle`
- `Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants`
- `Sheaf.GroupTheory.GroupAlgebraFunctorialInjectiveEmbeddings`
- `Sheaf.LinearAlgebra.IdempotentEndomorphismCharpolyField`
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
- `Sheaf.Paper.EtaleStandardCoverCech`
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
- `Sheaf.Paper.SheavesKilledByNZmodModules`
- `Sheaf.Paper.SimplicialSetAddSimplices`
- `Sheaf.Paper.SiteCoveringMorphismsSameH0Map`
- `Sheaf.Paper.SitePlusInjectiveSeparated`
- `Sheaf.Paper.SitePlusOfSeparatedIsSheaf`
- `Sheaf.Paper.SitePlusOfSheafIso`
- `Sheaf.Paper.SitePlusSeparated`
- `Sheaf.Paper.TrivialKanHomotopyEquivalence`
- `Sheaf.Paper.ZariskiH0ProperHenselianPair`
- `Sheaf.RepresentationTheory.CoinducedContinuousAcyclic`
- `Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding`
- `Sheaf.RepresentationTheory.CoinducedHomotopyContinuous`
- `Sheaf.RepresentationTheory.CoinducedHomotopyIdentity`
- `Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants`
- `Sheaf.RepresentationTheory.ContinuousCochainsShortExact`
- `Sheaf.RepresentationTheory.DiscreteContinuousCohomology`
- `Sheaf.RepresentationTheory.DiscreteContinuousFunctorialInjectives`
- `Sheaf.RepresentationTheory.DiscreteContinuousInjectives`
- `Sheaf.RepresentationTheory.DiscreteRep`
- `Sheaf.RepresentationTheory.LAdic`
- `Sheaf.RepresentationTheory.OpenStabilizerAdjunction`
- `Sheaf.RepresentationTheory.ProfiniteStableLattice`
- `Sheaf.RingTheory.FlatModuleCompletion`
- `Sheaf.RingTheory.GradedAlgebra.ShortExactGradedComponent`
- `Sheaf.RingTheory.HenselianPairPrimeConnected`
- `Sheaf.RingTheory.LimitFlatModules`
- `Sheaf.RingTheory.MapIntoHenselianColimit`
- `Sheaf.RingTheory.PrincipalMaximalDimOneRegular`
- `Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen`
- `Sheaf.RingTheory.TorStrictlyProZero`
- `Sheaf.RingTheory.UniversalFirstOrderThickening`
- `Sheaf.RingTheory.ValuationRingNormal`
- `Sheaf.Topology.ClosedPushforwardConstantRestriction`
- `Sheaf.Topology.ContinuousOpenNormalStabilizer`
- `Sheaf.Topology.ExistsUniqueIsGenericPointOfFinite`
- `Sheaf.Topology.FilteredInjectiveCechAcyclic`
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
