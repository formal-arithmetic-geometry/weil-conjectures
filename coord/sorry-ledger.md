# Sorry ledger

Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.
Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.
Progress = closed − added in the closure, with pruning reported separately.

Holes now: library **2362**, closure **1582**, holes in definitions **9**, definitions with undetermined data **4** (closure **2**).

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
| Sheaf | 2103 | 1540 |
| WeilConjectures | 259 | 42 |

| baseline | scope | closed | added | net | deleted | changed holed statements |
|---|---|---:|---:|---:|---:|---:|
| 889327369 (Queue at the start of stage 3) | library | 979 | 412 | 567 | 0 | 0 |
| 660345513 (Application of proof-dependency imports) | library | 904 | 393 | 511 | 0 | 0 |
| 660345513 (Application of proof-dependency imports) | closure | 888 | 372 | 516 | 0 | 0 |

No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.

| landing class | count |
|---|---:|
| proved | 708 |
| decomposed | 8 |
| moved | 638 |
| pruned | 32 |
| other | 4 |

Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.

| group | landings | closed | added | net | moved share |
|---|---:|---:|---:|---:|---:|
| A2 | 27 | 27 | 20 | 7 | 16/27 (59.3%) |
| A3 | 26 | 29 | 20 | 9 | 11/26 (42.3%) |
| B2 | 25 | 26 | 21 | 5 | 14/25 (56.0%) |
| B3 | 34 | 38 | 20 | 18 | 13/34 (38.2%) |
| C1 | 38 | 42 | 32 | 10 | 22/38 (57.9%) |
| C2 | 23 | 23 | 19 | 4 | 13/23 (56.5%) |
| C3 | 10 | 10 | 8 | 2 | 6/10 (60.0%) |
| D2 | 29 | 33 | 23 | 10 | 16/29 (55.2%) |
| D3 | 11 | 11 | 2 | 9 | 2/11 (18.2%) |
| E1 | 40 | 50 | 25 | 25 | 19/40 (47.5%) |
| E2 | 31 | 30 | 27 | 3 | 18/31 (58.1%) |
| E3 | 8 | 8 | 2 | 6 | 2/8 (25.0%) |
| F1 | 35 | 39 | 27 | 12 | 15/35 (42.9%) |
| F2 | 23 | 38 | 13 | 25 | 10/23 (43.5%) |
| F3 | 10 | 14 | 2 | 12 | 1/10 (10.0%) |
| G1 | 35 | 38 | 37 | 1 | 20/35 (57.1%) |
| G2 | 26 | 29 | 27 | 2 | 15/26 (57.7%) |
| G3 | 10 | 11 | 7 | 4 | 5/10 (50.0%) |
| H1 | 28 | 29 | 19 | 10 | 14/28 (50.0%) |
| H2 | 26 | 28 | 20 | 8 | 16/26 (61.5%) |
| H3 | 13 | 21 | 5 | 16 | 4/13 (30.8%) |
| J1 | 34 | 41 | 17 | 24 | 13/34 (38.2%) |
| J2 | 26 | 29 | 26 | 3 | 16/26 (61.5%) |
| J3 | 11 | 11 | 2 | 9 | 2/11 (18.2%) |
| K1 | 34 | 38 | 29 | 9 | 19/34 (55.9%) |
| K2 | 34 | 37 | 27 | 10 | 21/34 (61.8%) |
| K3 | 10 | 11 | 0 | 11 | 0/10 (0.0%) |
| M1 | 32 | 37 | 20 | 17 | 12/32 (37.5%) |
| M2 | 25 | 33 | 17 | 16 | 9/25 (36.0%) |
| M3 | 11 | 12 | 4 | 8 | 4/11 (36.4%) |
| N1 | 33 | 34 | 25 | 9 | 18/33 (54.5%) |
| N2 | 23 | 29 | 10 | 19 | 9/23 (39.1%) |
| N3 | 9 | 9 | 6 | 3 | 4/9 (44.4%) |
| P1 | 37 | 57 | 27 | 30 | 17/37 (45.9%) |
| P2 | 32 | 35 | 19 | 16 | 9/32 (28.1%) |
| P3 | 11 | 11 | 12 | -1 | 6/11 (54.5%) |
| Q1 | 24 | 26 | 16 | 10 | 11/24 (45.8%) |
| Q2 | 24 | 25 | 15 | 10 | 10/24 (41.7%) |
| Q3 | 11 | 12 | 8 | 4 | 4/11 (36.4%) |
| R1 | 34 | 44 | 21 | 23 | 13/34 (38.2%) |
| R2 | 26 | 29 | 19 | 10 | 13/26 (50.0%) |
| R3 | 9 | 12 | 0 | 12 | 0/9 (0.0%) |
| S1 | 31 | 34 | 30 | 4 | 17/31 (54.8%) |
| S2 | 29 | 31 | 26 | 5 | 15/29 (51.7%) |
| S3 | 9 | 11 | 2 | 9 | 2/9 (22.2%) |
| T1 | 34 | 35 | 27 | 8 | 16/34 (47.1%) |
| T2 | 25 | 35 | 14 | 21 | 9/25 (36.0%) |
| T3 | 8 | 8 | 7 | 1 | 4/8 (50.0%) |
| U1 | 37 | 43 | 34 | 9 | 23/37 (62.2%) |
| U2 | 32 | 32 | 20 | 12 | 13/32 (40.6%) |
| U3 | 8 | 8 | 3 | 5 | 2/8 (25.0%) |
| V1 | 35 | 34 | 15 | 19 | 12/35 (34.3%) |
| V2 | 26 | 27 | 23 | 4 | 14/26 (53.8%) |
| V3 | 14 | 18 | 8 | 10 | 6/14 (42.9%) |
| W2 | 25 | 27 | 10 | 17 | 8/25 (32.0%) |
| W3 | 11 | 11 | 5 | 6 | 3/11 (27.3%) |
| X2 | 28 | 28 | 28 | 0 | 15/28 (53.6%) |
| X3 | 7 | 8 | 4 | 4 | 2/7 (28.6%) |
| Y2 | 25 | 27 | 15 | 12 | 10/25 (40.0%) |
| Y3 | 7 | 8 | 6 | 2 | 5/7 (71.4%) |
| Z2 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |

Nearest targets (claims from the scanned git tree; live leases may differ):

| module | distance | holes | group |
|---|---:|---:|---|
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | 0 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | 0 | 1 | ORCHESTRA |
| WeilConjectures.AlgebraicGeometry.Curve.Reductions | 1 | 1 | A2 |
| Sheaf.AlgebraicGeometry.ProperGeometricPointExchange | 2 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.Gabber | 2 | 2 | S2 |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardOpenQuotientConstant | 3 | 1 | T2 |
| Sheaf.AlgebraicGeometry.Curve.NormalizationComparisonOnIsoLocus | 3 | 1 | — |
| Sheaf.AlgebraicGeometry.EtaleH0FiniteConnectedCriterion | 3 | 1 | ORCHESTRA |
| Sheaf.AlgebraicGeometry.EtaleSectionsBaseFieldExtension | 3 | 1 | ORCHESTRA |
| WeilConjectures.AlgebraicGeometry.HenselianConnectedness | 3 | 1 | ORCHESTRA |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | 3 | 4 | — |
| Sheaf.AlgebraicGeometry.Curve.FilteredFiniteCoverLowerShriekTransferCore | 4 | 1 | V1 |
| Sheaf.AlgebraicGeometry.EtaleSetSectionsFlatConnectedFibres | 4 | 1 | ORCHESTRA |
| Sheaf.AlgebraicGeometry.ProjectiveLineCompatibleStrictHenselizationResiduesCore | 4 | 2 | R2 |
| Sheaf.AlgebraicGeometry.StrictHenselization | 4 | 2 | K2 |
| Sheaf.FieldTheory.FieldTensorUniqueMinimalPrime | 4 | 1 | ORCHESTRA |
| Sheaf.Paper.StrictHenselizationPointedMap | 4 | 2 | W2 |
| Sheaf.AlgebraicGeometry.Cohomology.FlatCohomologyCechCocycles | 5 | 1 | T2 |
| Sheaf.AlgebraicGeometry.ConstantExtensionCokernelAux | 5 | 2 | W2 |
| Sheaf.AlgebraicGeometry.Curve.LowerShriekCoefficientCounit | 5 | 1 | U2 |

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
- `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution`
- `Sheaf.AlgebraicTopology.SimplicialIndexFiniteInitial`
- `Sheaf.CategoryTheory.AdjunctionTransferFunctorialInjectives`
- `Sheaf.CategoryTheory.BoundedSubobjectSize`
- `Sheaf.CategoryTheory.BoundedSubobjectSurjection`
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
