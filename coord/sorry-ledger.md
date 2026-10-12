# Sorry ledger

Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.
Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.
Progress = closed − added in the closure, with pruning reported separately.

Holes now: library **2080**, closure **1263**, holes in definitions **9**, definitions with undetermined data **4** (closure **2**).

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
- `Sheaf.AlgebraicGeometry.GlobalHomAdjunctionIso::AlgebraicGeometry.schemeHomTensorPullbackIso` (line 271), chosen from `AlgebraicGeometry.exists_schemeHomTensorPullbackIso`
- `Sheaf.Paper.LisseAdicFiberFunctors::AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor` (line 144), chosen from `AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor_exists`
- `Sheaf.Paper.LisseAdicSheaves::AlgebraicGeometry.Scheme.lisseCoefficientDiagramData` (line 527), chosen from `AlgebraicGeometry.Scheme.lisseCoefficientDiagram_exists`

| root | library | closure |
|---|---:|---:|
| Sheaf | 1829 | 1229 |
| WeilConjectures | 251 | 34 |

| baseline | scope | closed | added | net | deleted | changed holed statements |
|---|---|---:|---:|---:|---:|---:|
| 889327369 (Queue at the start of stage 3) | library | 1313 | 464 | 849 | 0 | 1 |
| 660345513 (Application of proof-dependency imports) | library | 1243 | 450 | 793 | 0 | 1 |
| 660345513 (Application of proof-dependency imports) | closure | 1213 | 409 | 804 | 0 | 0 |

No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.

| landing class | count |
|---|---:|
| proved | 1138 |
| decomposed | 12 |
| moved | 1119 |
| pruned | 57 |
| other | 11 |

Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.

| group | landings | closed | added | net | moved share |
|---|---:|---:|---:|---:|---:|
| A2 | 44 | 44 | 33 | 11 | 24/44 (54.5%) |
| A3 | 46 | 52 | 29 | 23 | 18/46 (39.1%) |
| B2 | 44 | 48 | 36 | 12 | 24/44 (54.5%) |
| B3 | 51 | 55 | 31 | 24 | 21/51 (41.2%) |
| C1 | 50 | 57 | 41 | 16 | 28/50 (56.0%) |
| C2 | 37 | 37 | 29 | 8 | 19/37 (51.4%) |
| C3 | 27 | 28 | 18 | 10 | 13/27 (48.1%) |
| D2 | 52 | 56 | 39 | 17 | 27/52 (51.9%) |
| D3 | 29 | 40 | 19 | 21 | 12/29 (41.4%) |
| E1 | 50 | 60 | 33 | 27 | 26/50 (52.0%) |
| E2 | 45 | 45 | 39 | 6 | 26/45 (57.8%) |
| E3 | 26 | 27 | 17 | 10 | 11/26 (42.3%) |
| F1 | 51 | 57 | 39 | 18 | 23/51 (45.1%) |
| F2 | 44 | 59 | 35 | 24 | 21/44 (47.7%) |
| F3 | 28 | 31 | 13 | 18 | 9/28 (32.1%) |
| G1 | 52 | 55 | 51 | 4 | 29/52 (55.8%) |
| G2 | 48 | 53 | 40 | 13 | 23/48 (47.9%) |
| G3 | 26 | 32 | 17 | 15 | 12/26 (46.2%) |
| H1 | 45 | 46 | 33 | 13 | 24/45 (53.3%) |
| H2 | 38 | 40 | 29 | 11 | 21/38 (55.3%) |
| H3 | 33 | 41 | 26 | 15 | 21/33 (63.6%) |
| J1 | 48 | 55 | 22 | 33 | 17/48 (35.4%) |
| J2 | 42 | 46 | 37 | 9 | 26/42 (61.9%) |
| J3 | 29 | 31 | 6 | 25 | 5/29 (17.2%) |
| K1 | 46 | 50 | 35 | 15 | 24/46 (52.2%) |
| K2 | 51 | 55 | 36 | 19 | 29/51 (56.9%) |
| K3 | 26 | 27 | 12 | 15 | 11/26 (42.3%) |
| M1 | 55 | 58 | 31 | 27 | 21/55 (38.2%) |
| M2 | 44 | 52 | 32 | 20 | 20/44 (45.5%) |
| M3 | 23 | 23 | 13 | 10 | 12/23 (52.2%) |
| N1 | 49 | 51 | 41 | 10 | 28/49 (57.1%) |
| N2 | 39 | 44 | 26 | 18 | 19/39 (48.7%) |
| N3 | 19 | 18 | 11 | 7 | 9/19 (47.4%) |
| P1 | 53 | 74 | 39 | 35 | 26/53 (49.1%) |
| P2 | 53 | 55 | 27 | 28 | 16/53 (30.2%) |
| P3 | 28 | 29 | 22 | 7 | 12/28 (42.9%) |
| Q1 | 42 | 44 | 29 | 15 | 21/42 (50.0%) |
| Q2 | 37 | 38 | 27 | 11 | 17/37 (45.9%) |
| Q3 | 22 | 26 | 14 | 12 | 8/22 (36.4%) |
| R1 | 52 | 63 | 36 | 27 | 23/52 (44.2%) |
| R2 | 45 | 48 | 34 | 14 | 22/45 (48.9%) |
| R3 | 24 | 28 | 12 | 16 | 8/24 (33.3%) |
| S1 | 48 | 51 | 48 | 3 | 27/48 (56.2%) |
| S2 | 44 | 48 | 33 | 15 | 20/44 (45.5%) |
| S3 | 20 | 22 | 11 | 11 | 9/20 (45.0%) |
| T1 | 44 | 45 | 36 | 9 | 23/44 (52.3%) |
| T2 | 39 | 49 | 26 | 23 | 18/39 (46.2%) |
| T3 | 21 | 22 | 21 | 1 | 12/21 (57.1%) |
| U1 | 55 | 64 | 48 | 16 | 33/55 (60.0%) |
| U2 | 43 | 43 | 28 | 15 | 20/43 (46.5%) |
| U3 | 22 | 22 | 14 | 8 | 11/22 (50.0%) |
| V1 | 47 | 46 | 25 | 21 | 18/47 (38.3%) |
| V2 | 38 | 41 | 32 | 9 | 20/38 (52.6%) |
| V3 | 29 | 32 | 16 | 16 | 13/29 (44.8%) |
| W2 | 40 | 43 | 17 | 26 | 13/40 (32.5%) |
| W3 | 28 | 28 | 17 | 11 | 12/28 (42.9%) |
| X2 | 43 | 43 | 40 | 3 | 22/43 (51.2%) |
| X3 | 17 | 18 | 12 | 6 | 8/17 (47.1%) |
| Y2 | 43 | 45 | 31 | 14 | 20/43 (46.5%) |
| Y3 | 20 | 21 | 16 | 5 | 13/20 (65.0%) |
| Z2 | 3 | 4 | 0 | 4 | 1/3 (33.3%) |

Nearest targets (claims from the scanned git tree; live leases may differ):

| module | distance | holes | group |
|---|---:|---:|---|
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | 0 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | 0 | 1 | ORCHESTRA |
| Sheaf.AlgebraicGeometry.Curve.FinitePushforwardModuleAssertions | 2 | 1 | P2 |
| Sheaf.AlgebraicGeometry.Curve.NormalizationAssertionsTransfer | 2 | 1 | M1 |
| WeilConjectures.SixFunctors.Etale.Gabber | 2 | 2 | N2 |
| Sheaf.AlgebraicGeometry.Curve.NormalizationComparisonOnIsoLocus | 3 | 1 | — |
| Sheaf.AlgebraicGeometry.FinitePushforwardFiniteStalkModule | 3 | 1 | S2 |
| WeilConjectures.ConstructibleSheaf.FinitePushforward | 3 | 4 | — |
| Sheaf.AlgebraicGeometry.QcqsStrictLocalModuleComparison | 4 | 1 | T1 |
| Sheaf.AlgebraicGeometry.StrictLocalExchangeCompatibility | 4 | 1 | U3 |
| Sheaf.Paper.StrictHenselizationPointedMap | 4 | 2 | Y2 |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueImage | 5 | 1 | F1 |
| Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift | 5 | 1 | — |
| Sheaf.AlgebraicGeometry.ConstantExtensionPresentationLift | 5 | 1 | J3 |
| Sheaf.AlgebraicGeometry.Curve.FiniteEtaleCoverReducedCompactification | 5 | 1 | F3 |
| Sheaf.AlgebraicGeometry.Curve.PrimeModuleFiniteOpenAssertionsTransfer | 5 | 1 | F2 |
| Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEquivalence | 5 | 1 | F1 |
| Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic | 5 | 1 | V2 |
| WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex | 5 | 1 | E2 |
| WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations | 5 | 6 | X3 |

Modules pruned since the imports baseline:

- `Sheaf.Algebra.Category.ModuleCat.RingScalarExtension`
- `Sheaf.Algebra.CharpolyLocallyFree`
- `Sheaf.Algebra.Homology.AcyclicLimitOrdinal`
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`
- `Sheaf.Algebra.Homology.FunctorialHomotopies`
- `Sheaf.Algebra.Homology.LowerTruncationStepSES`
- `Sheaf.Algebra.Homology.MappingCylinderSplitFactorization`
- `Sheaf.Algebra.Homology.MittagLefflerLimitHomology`
- `Sheaf.Algebra.Homology.SubcategoryRightResolution`
- `Sheaf.Algebra.LocallyFreeCharpoly`
- `Sheaf.Algebra.LocallyFreeCharpolyProdMap`
- `Sheaf.Algebra.Module.ProjDegreeZeroLocalizationExact`
- `Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize`
- `Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`
- `Sheaf.AlgebraicGeometry.ConductorIdealRestriction`
- `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural`
- `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
- `Sheaf.AlgebraicGeometry.DescendFiniteLocallyFree`
- `Sheaf.AlgebraicGeometry.DescendFlatFinitePresentation`
- `Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek`
- `Sheaf.AlgebraicGeometry.DvrFieldExtensionOrder`
- `Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `Sheaf.AlgebraicGeometry.FibreProductLimit`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `Sheaf.AlgebraicGeometry.FiniteAffineFibreSections`
- `Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen`
- `Sheaf.AlgebraicGeometry.FiniteDiscreteSeparatedAffine`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`
- `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`
- `Sheaf.AlgebraicGeometry.FinitePresentationKernelSurjectionFiniteType`
- `Sheaf.AlgebraicGeometry.FiniteSeparableMultiplicationEtale`
- `Sheaf.AlgebraicGeometry.FirstOrderThickeningBaseChange`
- `Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections`
- `Sheaf.AlgebraicGeometry.FlatModulePullbackExact`
- `Sheaf.AlgebraicGeometry.FlatUnramifiedFormallyEtale`
- `Sheaf.AlgebraicGeometry.FormallySmooth`
- `Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal`
- `Sheaf.AlgebraicGeometry.FpqcAffineDescent`
- `Sheaf.AlgebraicGeometry.FpqcAffineStandardRefinement`
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`
- `Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion`
- `Sheaf.AlgebraicGeometry.FpqcTensorSections`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer`
- `Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection`
- `Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting`
- `Sheaf.AlgebraicGeometry.HypercoverOneMoreSimplex`
- `Sheaf.AlgebraicGeometry.KoszulRegularImmersionDerivedHom`
- `Sheaf.AlgebraicGeometry.LftOverFieldIsolatedPointResidueFinite`
- `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty`
- `Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent`
- `Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope`
- `Sheaf.AlgebraicGeometry.NagataFixedBaseSeparatedStage`
- `Sheaf.AlgebraicGeometry.NormalizationProperties`
- `Sheaf.AlgebraicGeometry.ProjStandardOpenBasis`
- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition`
- `Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange`
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
- `Sheaf.AlgebraicGeometry.TensorGeneratingSections`
- `Sheaf.AlgebraicGeometry.TensorGloballyGenerated`
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
- `Sheaf.CategoryTheory.ColimitSiteCechComplex`
- `Sheaf.CategoryTheory.CoskeletonMatchingTuples`
- `Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification`
- `Sheaf.CategoryTheory.DerivedCoupleFunctoriality`
- `Sheaf.CategoryTheory.DerivedFunctorInverts`
- `Sheaf.CategoryTheory.DiscreteModulesAbelian`
- `Sheaf.CategoryTheory.EdgeCollapse`
- `Sheaf.CategoryTheory.EquivalenceInternalModule`
- `Sheaf.CategoryTheory.EssentiallyConstantSplitting`
- `Sheaf.CategoryTheory.EssentiallyConstantSystem`
- `Sheaf.CategoryTheory.ExactCoupleMorphism`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.CategoryTheory.FiniteContinuousModule`
- `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`
- `Sheaf.CategoryTheory.Galois.AbstractEquivalence`
- `Sheaf.CategoryTheory.Galois.AutProfinite`
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
- `Sheaf.CategoryTheory.InjectiveResolutionSESComplexes`
- `Sheaf.CategoryTheory.InternalModule`
- `Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact`
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`
- `Sheaf.CategoryTheory.MittagLefflerExactSequence`
- `Sheaf.CategoryTheory.MittagLefflerLimitExact`
- `Sheaf.CategoryTheory.ProperFaceMatchingObject`
- `Sheaf.CategoryTheory.PushoutShortExactSequence`
- `Sheaf.CategoryTheory.QuotientJShriek`
- `Sheaf.CategoryTheory.SimplicialMatchingObject`
- `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement`
- `Sheaf.CategoryTheory.SiteLerayDegenerate`
- `Sheaf.CategoryTheory.Sites.BinaryContractedProductPresentation`
- `Sheaf.CategoryTheory.Sites.CoherentContractedPowers`
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `Sheaf.CategoryTheory.Sites.CohomologySiteEquivalence`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorPushoutExtension`
- `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`
- `Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf`
- `Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation`
- `Sheaf.CategoryTheory.Sites.TorsorH1Functoriality`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtension`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtensionPresentation`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerTorsor`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedProductPresentation`
- `Sheaf.CategoryTheory.Sites.ZariskiExtTorsor`
- `Sheaf.CategoryTheory.Sites.ZariskiTorsorExtensionPushout`
- `Sheaf.CategoryTheory.SpectralSequenceComparison`
- `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`
- `Sheaf.CategoryTheory.TruncationCoupleExact`
- `Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`
- `Sheaf.FieldTheory.SeparatingTranscendenceBasisFiniteSubextension`
- `Sheaf.GroupTheory.GroupAlgebraFunctorialInjectiveEmbeddings`
- `Sheaf.LinearAlgebra.IdempotentEndomorphismCharpolyField`
- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`
- `Sheaf.NumberTheory.Padics.CoefficientExtension`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`
- `Sheaf.NumberTheory.Padics.LatticeStabilizerOpen`
- `Sheaf.Paper.AdicTowerReconstruction`
- `Sheaf.Paper.CechNerveFreeHomology`
- `Sheaf.Paper.ColimitSitesInjectiveSystem`
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
- `Sheaf.Paper.KoszulDifferentialSquareZero`
- `Sheaf.Paper.LisseAdicFiberFunctors`
- `Sheaf.Paper.LisseAdicSheaves`
- `Sheaf.Paper.LisseTensorScalarExtension`
- `Sheaf.Paper.PlusConstructionFunctorial`
- `Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange`
- `Sheaf.Paper.SheavesKilledByNZmodModules`
- `Sheaf.Paper.SimplicialSetAddSimplices`
- `Sheaf.Paper.SiteCoveringMorphismsSameH0Map`
- `Sheaf.Paper.SitePlusInjectiveSeparated`
- `Sheaf.Paper.SitePlusOfSeparatedIsSheaf`
- `Sheaf.Paper.SitePlusOfSheafIso`
- `Sheaf.Paper.SitePlusSeparated`
- `Sheaf.Paper.SiteRestrictionInjectives`
- `Sheaf.Paper.StrictlyHenselianEtaleAcyclic`
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
- `Sheaf.RingTheory.AnnihilatorLocalizationAway`
- `Sheaf.RingTheory.ColimitFlatRingMap`
- `Sheaf.RingTheory.FlatModuleCompletion`
- `Sheaf.RingTheory.GradedAlgebra.ShortExactGradedComponent`
- `Sheaf.RingTheory.IsolatedPrimeResidueFinite`
- `Sheaf.RingTheory.KrullIntersectionLocalization`
- `Sheaf.RingTheory.LimitFlatModules`
- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`
- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfStronglyTranscendental`
- `Sheaf.RingTheory.PopescuDesingularize`
- `Sheaf.RingTheory.PrincipalMaximalDimOneRegular`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePermanence`
- `Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen`
- `Sheaf.RingTheory.QuasiFiniteMonogenicIntegralClosure`
- `Sheaf.RingTheory.SeparablePolynomialQuotientReduced`
- `Sheaf.RingTheory.StrictlyStandardLocalizationSmooth`
- `Sheaf.RingTheory.TorStrictlyProZero`
- `Sheaf.RingTheory.UniversalFirstOrderThickening`
- `Sheaf.RingTheory.ValuationRingNormal`
- `Sheaf.Topology.AbelianCohomologyDeltaFunctor`
- `Sheaf.Topology.ClosedImmersionPushforwardExact`
- `Sheaf.Topology.ClosedPushforwardBoundaryNaturality`
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
- `Sheaf.Topology.StalkDirectSums`
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
