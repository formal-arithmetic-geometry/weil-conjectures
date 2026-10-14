# Sorry ledger

Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.
Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.
Progress = closed − added in the closure, with pruning reported separately.

Holes now: library **832**, closure **16**, holes in definitions **4**, definitions with undetermined data **2** (closure **0**).

Definitions with holes (def/instance/structure field):

- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup::<anonymous:instance : (derivedIdeal I).IsHopfIdeal k>` (instance, line 403)
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup::<anonymous:instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I))>` (instance, line 411)
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie::AlgebraicGeometry.GeneralLinearGroup.toMatrixLieHom` (def, line 110)
- `WeilConjectures.RingTheory.ProEtale.ClosedLift::Algebra.ClosedLift.isFiltered_index` (instance, line 142)

Definitions with undetermined data (class-1 exceptions in `coord/hollow-definitions.md`):

- `Sheaf.Paper.LisseAdicFiberFunctors::AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor` (line 144), chosen from `AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor_exists`
- `Sheaf.Paper.LisseAdicSheaves::AlgebraicGeometry.Scheme.lisseCoefficientDiagramData` (line 527), chosen from `AlgebraicGeometry.Scheme.lisseCoefficientDiagram_exists`

| root | library | closure |
|---|---:|---:|
| Sheaf | 620 | 14 |
| WeilConjectures | 212 | 2 |

| baseline | scope | closed | added | net | deleted | changed holed statements |
|---|---|---:|---:|---:|---:|---:|
| 889327369 (Queue at the start of stage 3) | library | 2178 | 87 | 2091 | 6 | 1 |
| 660345513 (Application of proof-dependency imports) | library | 2120 | 85 | 2035 | 6 | 1 |
| 660345513 (Application of proof-dependency imports) | closure | 1979 | 14 | 1965 | 4 | 0 |

No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.

| landing class | count |
|---|---:|
| proved | 3366 |
| decomposed | 48 |
| moved | 3899 |
| pruned | 119 |
| other | 466 |

Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.

| group | landings | closed | added | net | moved share |
|---|---:|---:|---:|---:|---:|
| A2 | 110 | 104 | 74 | 30 | 56/110 (50.9%) |
| A3 | 120 | 117 | 76 | 41 | 52/120 (43.3%) |
| A4 | 55 | 53 | 39 | 14 | 30/55 (54.5%) |
| B2 | 119 | 113 | 81 | 32 | 50/119 (42.0%) |
| B3 | 129 | 133 | 80 | 53 | 56/129 (43.4%) |
| B4 | 53 | 44 | 38 | 6 | 27/53 (50.9%) |
| C1 | 133 | 137 | 104 | 33 | 70/133 (52.6%) |
| C2 | 111 | 104 | 76 | 28 | 51/111 (45.9%) |
| C3 | 107 | 106 | 74 | 32 | 52/107 (48.6%) |
| C4 | 39 | 33 | 28 | 5 | 18/39 (46.2%) |
| D2 | 128 | 126 | 86 | 40 | 59/128 (46.1%) |
| D3 | 96 | 101 | 66 | 35 | 47/96 (49.0%) |
| D4 | 50 | 45 | 41 | 4 | 25/50 (50.0%) |
| E1 | 143 | 158 | 103 | 55 | 79/143 (55.2%) |
| E2 | 108 | 105 | 81 | 24 | 56/108 (51.9%) |
| E3 | 104 | 99 | 85 | 14 | 56/104 (53.8%) |
| E4 | 37 | 37 | 26 | 11 | 19/37 (51.4%) |
| F1 | 134 | 135 | 103 | 32 | 69/134 (51.5%) |
| F2 | 133 | 134 | 98 | 36 | 61/133 (45.9%) |
| F3 | 85 | 86 | 55 | 31 | 39/85 (45.9%) |
| F4 | 50 | 43 | 36 | 7 | 25/50 (50.0%) |
| G1 | 135 | 136 | 111 | 25 | 74/135 (54.8%) |
| G2 | 132 | 131 | 88 | 43 | 60/132 (45.5%) |
| G3 | 97 | 100 | 66 | 34 | 45/97 (46.4%) |
| G4 | 52 | 44 | 28 | 16 | 18/52 (34.6%) |
| H1 | 130 | 128 | 105 | 23 | 73/130 (56.2%) |
| H2 | 108 | 106 | 88 | 18 | 64/108 (59.3%) |
| H3 | 118 | 133 | 94 | 39 | 65/118 (55.1%) |
| H4 | 55 | 52 | 41 | 11 | 30/55 (54.5%) |
| J1 | 122 | 129 | 75 | 54 | 53/122 (43.4%) |
| J2 | 102 | 104 | 70 | 34 | 51/102 (50.0%) |
| J3 | 115 | 121 | 76 | 45 | 53/115 (46.1%) |
| J4 | 59 | 51 | 39 | 12 | 26/59 (44.1%) |
| K1 | 115 | 128 | 87 | 41 | 58/115 (50.4%) |
| K2 | 119 | 117 | 83 | 34 | 64/119 (53.8%) |
| K3 | 105 | 105 | 75 | 30 | 55/105 (52.4%) |
| K4 | 59 | 44 | 34 | 10 | 24/59 (40.7%) |
| M1 | 136 | 135 | 92 | 43 | 65/136 (47.8%) |
| M2 | 127 | 129 | 103 | 26 | 69/127 (54.3%) |
| M3 | 105 | 106 | 71 | 35 | 51/105 (48.6%) |
| M4 | 43 | 43 | 23 | 20 | 16/43 (37.2%) |
| N1 | 132 | 134 | 108 | 26 | 74/132 (56.1%) |
| N2 | 127 | 116 | 78 | 38 | 57/127 (44.9%) |
| N3 | 86 | 81 | 65 | 16 | 45/86 (52.3%) |
| N4 | 54 | 52 | 48 | 4 | 29/54 (53.7%) |
| P1 | 116 | 136 | 91 | 45 | 65/116 (56.0%) |
| P2 | 129 | 121 | 79 | 42 | 54/129 (41.9%) |
| P3 | 100 | 93 | 81 | 12 | 52/100 (52.0%) |
| P4 | 51 | 47 | 39 | 8 | 26/51 (51.0%) |
| Q1 | 106 | 107 | 74 | 33 | 54/106 (50.9%) |
| Q2 | 103 | 106 | 79 | 27 | 52/103 (50.5%) |
| Q3 | 100 | 99 | 70 | 29 | 46/100 (46.0%) |
| Q4 | 46 | 49 | 26 | 23 | 20/46 (43.5%) |
| R1 | 122 | 126 | 97 | 29 | 67/122 (54.9%) |
| R2 | 120 | 120 | 75 | 45 | 52/120 (43.3%) |
| R3 | 93 | 90 | 65 | 25 | 42/93 (45.2%) |
| R4 | 56 | 47 | 41 | 6 | 26/56 (46.4%) |
| S1 | 123 | 125 | 104 | 21 | 68/123 (55.3%) |
| S2 | 121 | 125 | 98 | 27 | 63/121 (52.1%) |
| S3 | 102 | 97 | 63 | 34 | 48/102 (47.1%) |
| S4 | 44 | 42 | 34 | 8 | 23/44 (52.3%) |
| T1 | 108 | 108 | 80 | 28 | 55/108 (50.9%) |
| T2 | 131 | 153 | 97 | 56 | 64/131 (48.9%) |
| T3 | 98 | 93 | 75 | 18 | 52/98 (53.1%) |
| T4 | 65 | 58 | 38 | 20 | 24/65 (36.9%) |
| U1 | 125 | 126 | 92 | 34 | 62/125 (49.6%) |
| U2 | 135 | 129 | 92 | 37 | 63/135 (46.7%) |
| U3 | 95 | 97 | 69 | 28 | 49/95 (51.6%) |
| U4 | 51 | 45 | 40 | 5 | 28/51 (54.9%) |
| V1 | 112 | 105 | 85 | 20 | 55/112 (49.1%) |
| V2 | 125 | 122 | 89 | 33 | 61/125 (48.8%) |
| V3 | 106 | 110 | 74 | 36 | 55/106 (51.9%) |
| V4 | 49 | 43 | 36 | 7 | 24/49 (49.0%) |
| W2 | 113 | 118 | 78 | 40 | 54/113 (47.8%) |
| W3 | 83 | 83 | 58 | 25 | 40/83 (48.2%) |
| W4 | 47 | 43 | 36 | 7 | 27/47 (57.4%) |
| X2 | 119 | 116 | 94 | 22 | 63/119 (52.9%) |
| X3 | 100 | 95 | 62 | 33 | 43/100 (43.0%) |
| XR33076d633fce5c89 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR70f81a388df1a824 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR916f3f6fae119923 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR9e6d7250028f1981 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| XRa0a656f89c54729e | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRa2c5451bd4aff80a | 1 | 0 | 2 | -2 | 0/1 (0.0%) |
| XRa3e07659d1a5d330 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XRb0cc22400e136910 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRbb9b20b2b4a981ff | 2 | 0 | 0 | 0 | 0/2 (0.0%) |
| XRd4f549ddc0d8d578 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XReedb48d351b955d4 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRfef4bc449ceae451 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Y2 | 108 | 110 | 98 | 12 | 59/108 (54.6%) |
| Y3 | 103 | 90 | 56 | 34 | 45/103 (43.7%) |
| Z2 | 3 | 4 | 0 | 4 | 1/3 (33.3%) |

Nearest targets (claims from the scanned git tree; live leases may differ):

| module | distance | holes | group |
|---|---:|---:|---|
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.BaseChangeProperty | 0 | 1 | ORCHESTRA |
| WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine | 0 | 1 | ORCHESTRA |
| Sheaf.AlgebraicGeometry.BaseChangeTargetTransitionHigherImage | 11 | 1 | K3 |
| Sheaf.AlgebraicGeometry.CartesianHigherImageGermDescent | 12 | 1 | E1 |
| Sheaf.AlgebraicGeometry.CartesianHigherImageGermVanishing | 12 | 1 | R1 |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtSectionsFactorization | 23 | 1 | N1 |
| Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation | 24 | 1 | P1 |
| Sheaf.AlgebraicGeometry.ProperUnboundedBaseChange | 24 | 1 | P2 |
| Sheaf.AlgebraicGeometry.ProperGeometricPointDerivedCoproducts | 25 | 1 | P2 |
| Sheaf.AlgebraicGeometry.PicardResidueHomologyGeometricNaturalityFixedPerIndex | 28 | 1 | XR0d8c117f6f62b747 |
| Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility | 31 | 1 | W4 |
| Sheaf.Algebra.Homology.AffineTildeTensorOrdinaryExchange | 34 | 1 | P1 |
| Sheaf.Algebra.Homology.AffineTildeTensorSourceComparison | 34 | 1 | B3 |
| Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreData | 34 | 1 | A4 |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageRowsCore | 41 | 1 | A4 |
| Sheaf.AlgebraicGeometry.QCohOrdinaryTensorResolutionCoordinates | 50 | 1 | U3 |

Modules pruned since the imports baseline:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomIsSheaf`
- `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels`
- `Sheaf.Algebra.CharpolyLocallyFree`
- `Sheaf.Algebra.FiniteProjectiveTorAcyclic`
- `Sheaf.Algebra.Homology.AcyclicLimitOrdinal`
- `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`
- `Sheaf.Algebra.Homology.BalancedDerivedTensorModel`
- `Sheaf.Algebra.Homology.BaseChangeRHomPerfect`
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`
- `Sheaf.Algebra.Homology.DerivedTensorActionNaturality`
- `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology`
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`
- `Sheaf.Algebra.Homology.DerivedTensorTransitivity`
- `Sheaf.Algebra.Homology.FilteredColimitDerivedTensor`
- `Sheaf.Algebra.Homology.FilteredComplexZBDescription`
- `Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion`
- `Sheaf.Algebra.Homology.FunctorialHomotopies`
- `Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator`
- `Sheaf.Algebra.Homology.KInjectiveProducts`
- `Sheaf.Algebra.Homology.LowerTruncationStepSES`
- `Sheaf.Algebra.Homology.MittagLefflerLimitHomology`
- `Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap`
- `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange`
- `Sheaf.Algebra.Homology.SubcategoryRightResolution`
- `Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor`
- `Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor`
- `Sheaf.Algebra.LocallyFreeCharpoly`
- `Sheaf.Algebra.LocallyFreeCharpolyProdMap`
- `Sheaf.Algebra.Module.GradedLocalizationExact`
- `Sheaf.Algebra.Module.LocalizedHomogeneousPiece`
- `Sheaf.Algebra.Module.ProjDegreeZeroLocalizationExact`
- `Sheaf.Algebra.Module.QuotientPrimaryComponentNoTorsion`
- `Sheaf.Algebra.ProjectiveDimensionWellDefined`
- `Sheaf.Algebra.Schanuel`
- `Sheaf.AlgebraicGeometry.AffineCohomologyLocalization`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.AffineKoszulHomAlternatingCech`
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent`
- `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree`
- `Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat`
- `Sheaf.AlgebraicGeometry.AssociatedModule`
- `Sheaf.AlgebraicGeometry.AssociatedModuleHom`
- `Sheaf.AlgebraicGeometry.AssociatedModulePullback`
- `Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize`
- `Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints`
- `Sheaf.AlgebraicGeometry.ConductorIdealRestriction`
- `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural`
- `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric`
- `Sheaf.AlgebraicGeometry.Curve.EtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris`
- `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
- `Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`
- `Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek`
- `Sheaf.AlgebraicGeometry.DivisorClassCurve`
- `Sheaf.AlgebraicGeometry.DivisorModuleLocal`
- `Sheaf.AlgebraicGeometry.DvrFieldExtensionOrder`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent`
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `Sheaf.AlgebraicGeometry.FibreProductLimit`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `Sheaf.AlgebraicGeometry.FiniteAffineFibreSections`
- `Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen`
- `Sheaf.AlgebraicGeometry.FiniteDiscreteSeparatedAffine`
- `Sheaf.AlgebraicGeometry.FiniteIsolatedPointsOfFiniteType`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`
- `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`
- `Sheaf.AlgebraicGeometry.FiniteSeparableMultiplicationEtale`
- `Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent`
- `Sheaf.AlgebraicGeometry.FlatPrecomposePus`
- `Sheaf.AlgebraicGeometry.FpqcAffineDescent`
- `Sheaf.AlgebraicGeometry.FpqcAffineStandardRefinement`
- `Sheaf.AlgebraicGeometry.FpqcFinerThanEtale`
- `Sheaf.AlgebraicGeometry.FpqcLocalOnBaseCriterion`
- `Sheaf.AlgebraicGeometry.FpqcTensorSections`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`
- `Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer`
- `Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction`
- `Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`
- `Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy`
- `Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting`
- `Sheaf.AlgebraicGeometry.HypercoverOneMoreSimplex`
- `Sheaf.AlgebraicGeometry.InvertibleTensorQcoherent`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutions`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `Sheaf.AlgebraicGeometry.LftOverFieldIsolatedPointResidueFinite`
- `Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct`
- `Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis`
- `Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit`
- `Sheaf.AlgebraicGeometry.Modules.ModuleSkyscraperStalkAdjunction`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcOpenImmersionDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFpqcCover`
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent`
- `Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope`
- `Sheaf.AlgebraicGeometry.NagataFixedBaseSeparatedStage`
- `Sheaf.AlgebraicGeometry.NormalizationProperties`
- `Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom`
- `Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction`
- `Sheaf.AlgebraicGeometry.PresheafModuleStalkFilteredColimit`
- `Sheaf.AlgebraicGeometry.ProjStandardOpenBasis`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistGluedIdentification`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts`
- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition`
- `Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange`
- `Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`
- `Sheaf.AlgebraicGeometry.SRMatchingObjectOneMember`
- `Sheaf.AlgebraicGeometry.SchemeModulesFunctorialInjectiveEmbeddings`
- `Sheaf.AlgebraicGeometry.SchemeTheoreticUnion`
- `Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing`
- `Sheaf.AlgebraicGeometry.SemiRepresentableCoveringPermanence`
- `Sheaf.AlgebraicGeometry.SemiRepresentableObject`
- `Sheaf.AlgebraicGeometry.SimplicialHomObject`
- `Sheaf.AlgebraicGeometry.SimplicialHomObjectExists`
- `Sheaf.AlgebraicGeometry.SimplicialHomObjectPushout`
- `Sheaf.AlgebraicGeometry.SimplicialHomStandardSimplex`
- `Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`
- `Sheaf.AlgebraicGeometry.Sites.FiniteEtaleCoproductSections`
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`
- `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`
- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`
- `Sheaf.AlgebraicGeometry.SmoothZeroDifferentialsAffineOpenEtale`
- `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`
- `Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange`
- `Sheaf.AlgebraicGeometry.StandardFpqcQuotientTopology`
- `Sheaf.AlgebraicGeometry.StandardSmoothAffineDiagonalGenerators`
- `Sheaf.AlgebraicGeometry.TensorGeneratingSections`
- `Sheaf.AlgebraicGeometry.TensorGloballyGenerated`
- `Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover`
- `Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`
- `Sheaf.AlgebraicGeometry.UpperShriekRightAdjoint`
- `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`
- `Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan`
- `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`
- `Sheaf.AlgebraicTopology.GlueSimplex`
- `Sheaf.AlgebraicTopology.SimplicialIndexFiniteInitial`
- `Sheaf.CategoryTheory.Abelian.CompatibleNullHomotopyAssembly`
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
- `Sheaf.CategoryTheory.AdjunctionTransferFunctorialInjectives`
- `Sheaf.CategoryTheory.ArrowsFunctor`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.BoundedSubobjectSize`
- `Sheaf.CategoryTheory.BoundedSubobjectSurjection`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonHomotopy`
- `Sheaf.CategoryTheory.CartanEilenbergComparisonIndependence`
- `Sheaf.CategoryTheory.CartanEilenbergDoubleComplexHomotopy`
- `Sheaf.CategoryTheory.CartanEilenbergFunctorial`
- `Sheaf.CategoryTheory.CartanEilenbergProperties`
- `Sheaf.CategoryTheory.CartanEilenbergVerticalNullhomotopy`
- `Sheaf.CategoryTheory.CohomologyColimitSites`
- `Sheaf.CategoryTheory.ColimitSiteCechComplex`
- `Sheaf.CategoryTheory.ColimitSiteSections`
- `Sheaf.CategoryTheory.ColimitSites`
- `Sheaf.CategoryTheory.CoskeletonMatchingTuples`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit`
- `Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification`
- `Sheaf.CategoryTheory.DerivedFunctorInverts`
- `Sheaf.CategoryTheory.DiscreteModulesAbelian`
- `Sheaf.CategoryTheory.EdgeCollapse`
- `Sheaf.CategoryTheory.EquivalenceInternalModule`
- `Sheaf.CategoryTheory.EssentiallyConstantSplitting`
- `Sheaf.CategoryTheory.EssentiallyConstantSystem`
- `Sheaf.CategoryTheory.ExactCoupleMorphism`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.CategoryTheory.FilteredColimitCategories`
- `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence`
- `Sheaf.CategoryTheory.FilteredPageTwoModel`
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
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `Sheaf.CategoryTheory.HalfPlaneGradedCanonical`
- `Sheaf.CategoryTheory.HomotopyHomExactOfInjective`
- `Sheaf.CategoryTheory.HomotopyLimitVanishing`
- `Sheaf.CategoryTheory.HorizontalComparisonLift`
- `Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator`
- `Sheaf.CategoryTheory.InjectiveResolutionSESComplexes`
- `Sheaf.CategoryTheory.InternalModule`
- `Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact`
- `Sheaf.CategoryTheory.LocalizationHomColimit`
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`
- `Sheaf.CategoryTheory.MittagLefflerExactSequence`
- `Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets`
- `Sheaf.CategoryTheory.OpcyclesTorSurjection`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.ProperFaceMatchingObject`
- `Sheaf.CategoryTheory.PushoutShortExactSequence`
- `Sheaf.CategoryTheory.QuotientJShriek`
- `Sheaf.CategoryTheory.RightLocalizationHomColimit`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Sheaf.CategoryTheory.SimplicialMatchingObject`
- `Sheaf.CategoryTheory.SiteCohomologyPullback`
- `Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf`
- `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement`
- `Sheaf.CategoryTheory.SiteEquivalenceMorphismOfSites`
- `Sheaf.CategoryTheory.SiteEquivalenceMorphismTransport`
- `Sheaf.CategoryTheory.SiteFilteredColimitSections`
- `Sheaf.CategoryTheory.SiteLerayDegenerate`
- `Sheaf.CategoryTheory.SiteMorphismComposition`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.CategoryTheory.SiteSystemStrictification`
- `Sheaf.CategoryTheory.Sites.BinaryContractedProductPresentation`
- `Sheaf.CategoryTheory.Sites.CoherentContractedPowers`
- `Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization`
- `Sheaf.CategoryTheory.Sites.CohomologySiteEquivalence`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorPushoutExtension`
- `Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic`
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
- `Sheaf.CategoryTheory.SpectralSequencePageInduction`
- `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`
- `Sheaf.CategoryTheory.TruncationCoupleExact`
- `Sheaf.CategoryTheory.TruncationDescends`
- `Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`
- `Sheaf.FieldTheory.SeparableRootPthPower`
- `Sheaf.FieldTheory.SeparatingTranscendenceBasisFiniteSubextension`
- `Sheaf.LinearAlgebra.IdempotentEndomorphismCharpolyField`
- `Sheaf.LinearAlgebra.SplitExtensionFreePresentation`
- `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`
- `Sheaf.LinearAlgebra.TriangularChangeOfBasis`
- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`
- `Sheaf.NumberTheory.Padics.CoefficientExtension`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`
- `Sheaf.NumberTheory.Padics.LatticeStabilizerOpen`
- `Sheaf.Paper.AdicTowerReconstruction`
- `Sheaf.Paper.AffineProjectiveComplexDerivedHom`
- `Sheaf.Paper.CartanEilenbergLeftExactCohomology`
- `Sheaf.Paper.CechNerveFreeHomology`
- `Sheaf.Paper.ColimitSitesInjectiveSystem`
- `Sheaf.Paper.ColimitSurjectiveRingMap`
- `Sheaf.Paper.ConstantSheafOpenMaps`
- `Sheaf.Paper.CyclicExtensionCocycle`
- `Sheaf.Paper.DerivationExtendsFiniteType`
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`
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
- `Sheaf.Paper.ReducedSourceFactors`
- `Sheaf.Paper.SectionsOverQuasiCompactOpen`
- `Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange`
- `Sheaf.Paper.SheavesKilledByNZmodModules`
- `Sheaf.Paper.SimplicialSetAddSimplices`
- `Sheaf.Paper.SiteCoveringIsomorphicFamily`
- `Sheaf.Paper.SiteCoveringMorphismsSameH0Map`
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`
- `Sheaf.Paper.SitePlusInjectiveSeparated`
- `Sheaf.Paper.SitePlusOfSeparatedIsSheaf`
- `Sheaf.Paper.SitePlusOfSheafIso`
- `Sheaf.Paper.SitePlusSeparated`
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
- `Sheaf.RepresentationTheory.DiscreteContinuousInjectives`
- `Sheaf.RepresentationTheory.DiscreteRep`
- `Sheaf.RepresentationTheory.LAdic`
- `Sheaf.RepresentationTheory.ProfiniteStableLattice`
- `Sheaf.RingTheory.AnnihilatorLocalizationAway`
- `Sheaf.RingTheory.AssociatedPrimeLocalizeAtPrime`
- `Sheaf.RingTheory.ColimitCategoryFpAlgebras`
- `Sheaf.RingTheory.CompletedModuleAssociatedGradedGenerators`
- `Sheaf.RingTheory.CompletionFiniteQuotient`
- `Sheaf.RingTheory.ConormalGeneratorsGlobalCompleteIntersection`
- `Sheaf.RingTheory.DVRValuationRingCharacterization`
- `Sheaf.RingTheory.DirectedUnionSubringsFlatModule`
- `Sheaf.RingTheory.Etale.QuasiFiniteAtPrime`
- `Sheaf.RingTheory.EtaleFiniteFactorDecomposition`
- `Sheaf.RingTheory.EtaleRetractionFiniteTypeSplitting`
- `Sheaf.RingTheory.ExistsNegativeValuationOfTensorSurjective`
- `Sheaf.RingTheory.FiniteIffFormalGlueing`
- `Sheaf.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover`
- `Sheaf.RingTheory.FiniteProjectiveOfStandardCover`
- `Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit`
- `Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes`
- `Sheaf.RingTheory.GradedAlgebra.ShortExactGradedComponent`
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`
- `Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition`
- `Sheaf.RingTheory.IsolatedPrimeResidueFinite`
- `Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal`
- `Sheaf.RingTheory.KrullIntersectionLocalization`
- `Sheaf.RingTheory.LocalCompleteIntersectionFieldChange`
- `Sheaf.RingTheory.LocalDimensionZeroHenselian`
- `Sheaf.RingTheory.ModuleLocalizationFilteredColimit`
- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`
- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfStronglyTranscendental`
- `Sheaf.RingTheory.PolynomialDistinctLinearCRT`
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`
- `Sheaf.RingTheory.PowerSeriesFieldCohenFsAdic`
- `Sheaf.RingTheory.PrescribedResidueBasisSpreads`
- `Sheaf.RingTheory.PresentationsHomotopyEquivalent`
- `Sheaf.RingTheory.PrincipalMaximalDimOneRegular`
- `Sheaf.RingTheory.ProjectiveDimensionSESKernel`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePermanence`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization`
- `Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen`
- `Sheaf.RingTheory.QuasiFiniteLocusOpen`
- `Sheaf.RingTheory.QuasiFiniteMonogenicIntegralClosure`
- `Sheaf.RingTheory.RadicialPrimeUniqueDegreeP`
- `Sheaf.RingTheory.ReducedIdealsZeroIntersection`
- `Sheaf.RingTheory.RegularSequenceShortExactSequence`
- `Sheaf.RingTheory.RegularSequenceSwapTwo`
- `Sheaf.RingTheory.SeparablePolynomialQuotientReduced`
- `Sheaf.RingTheory.SplitInjectionAfterCompletion`
- `Sheaf.RingTheory.TorStrictlyProZero`
- `Sheaf.RingTheory.ValuationRingNormal`
- `Sheaf.RingTheory.ZariskisMainAway`
- `Sheaf.Topology.AbelianCohomologyDeltaFunctor`
- `Sheaf.Topology.BasisSheafSectionsGerms`
- `Sheaf.Topology.ClosedPushforwardBoundaryNaturality`
- `Sheaf.Topology.ClosedPushforwardConstantRestriction`
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
- `Sheaf.Topology.SheavesDirectedColimitSections`
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
- `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`
- `WeilConjectures.AlgebraicGeometry.Curve.DivisorSequence`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension`

Scanner limitations: macro-generated declarations, elaborated anonymous/private names, and tactic dependencies cannot be recovered from source. Synthetic names are source keys, not elaborated names.

Diagnostics:

- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup: anonymous holed declaration: <anonymous:instance : (derivedIdeal I).IsHopfIdeal k>
- WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup: anonymous holed declaration: <anonymous:instance : IsMonHom.ContainsCommutators (subgroupSchemeHom (le_derivedIdeal I))>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderRetracts>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ>
