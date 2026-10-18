# Sorry ledger

Source scan; one hole per declaration, regardless of token count. Deleted declarations are not proofs.
Closure is the queue’s import upper bound. Classes use source references, not elaborated dependencies.
Progress = closed − added in the closure, with pruning reported separately.

Holes now: library **1261**, closure **285**, holes in definitions **13**, definitions with undetermined data **28** (closure **8**).

Definitions with holes (def/instance/structure field):

- `Sheaf.AlgebraicGeometry.TruncationExchangeCouple::CategoryTheory.TruncationExchange.couple` (def, line 346)
- `Sheaf.CategoryTheory.FilteredHomologyExactCouple::CategoryTheory.filteredHomologyEIso` (def, line 36)
- `Sheaf.CategoryTheory.FilteredHomologyExactCouple::CategoryTheory.filteredHomologyExactCouple` (def, line 29)
- `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization::AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars` (instance, line 175)
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek::AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek` (instance, line 177)
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible::AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible` (instance, line 438)
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible::AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible` (instance, line 429)
- `WeilConjectures.TraceFormula.Slop.Basic::AlgebraicGeometry.ProEtale.CondensedRing.Slop.boundedConstructibleLowerShriekComp` (def, line 144)
- `WeilConjectures.TraceFormula.Slop.Basic::AlgebraicGeometry.ProEtale.CondensedRing.Slop.unitEndRingEquiv` (def, line 160)
- `WeilConjectures.TraceFormula.Slop.Correspondence::AlgebraicGeometry.ProEtale.CondensedRing.Slop.Correspondence.traceClass` (def, line 206)
- `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek::AlgebraicGeometry.ProEtale.CondensedRing.isEquivalence_boundedConstructibleUpperStar_of_iso` (instance, line 90)
- `WeilConjectures.WeilObject.BoundedConstructible.TensorHom::AlgebraicGeometry.ProEtale.CondensedRing.isIso_weilHomComparisonApp` (instance, line 181)
- `WeilConjectures.WeilObject.BoundedConstructible.TensorHom::AlgebraicGeometry.ProEtale.CondensedRing.weilTensorComparison` (def, line 89)

Definitions with undetermined data (class-1 exceptions in `coord/hollow-definitions.md`):

- `Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison::AlgebraicGeometry.Scheme.Modules.normalizedCoherentEtaleComparison` (line 130), chosen from `AlgebraicGeometry.Scheme.Modules.exists_unique_normalizedCoherentEtaleComparison`
- `Sheaf.AlgebraicGeometry.EtaleModuleStalkSpecialization::AlgebraicGeometry.Scheme.etaleModuleStalkSpecialization` (line 81), chosen from `AlgebraicGeometry.Scheme.existsUnique_etaleModuleStalkSpecialization`
- `Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf::AlgebraicGeometry.Etale.localAcyclicityStrictMap` (line 54), chosen from `AlgebraicGeometry.Etale.existsUnique_localAcyclicityStrictMap`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction::AlgebraicGeometry.Scheme.proEtaleRingRestrictionDerivedDirectImage` (line 222), chosen from `AlgebraicGeometry.Scheme.proEtaleRingRestrictionDerivedDirectImage_existsUnique`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction::AlgebraicGeometry.Scheme.proEtaleRingRestrictionDirectImage` (line 103), chosen from `AlgebraicGeometry.Scheme.proEtaleRingRestrictionDirectImage_existsUnique`
- `Sheaf.AlgebraicGeometry.ProperOpenComparison::AlgebraicGeometry.Etale.properOpenIdentification` (line 67), chosen from `AlgebraicGeometry.Etale.clopenSectionDirectImage`
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace::AlgebraicGeometry.RelativeProjectiveSpace.affinePolynomialEquiv` (line 193), chosen from `AlgebraicGeometry.RelativeProjectiveSpace.existsUnique_affinePolynomialEquiv`
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace::AlgebraicGeometry.RelativeProjectiveSpace.algebra` (line 140), chosen from `AlgebraicGeometry.RelativeProjectiveSpace.existsUnique_symmetricInput`
- `Sheaf.AlgebraicGeometry.RelativeProjectiveSpace::AlgebraicGeometry.RelativeProjectiveSpace.construction` (line 145), chosen from `AlgebraicGeometry.exists_relativeProjData`
- `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap::AlgebraicGeometry.Scheme.strictHenselizationMap` (line 48), chosen from `AlgebraicGeometry.Scheme.strictHenselizationMap_existsUnique`
- `Sheaf.CategoryTheory.ScalarLocalization::CategoryTheory.ScalarLocalization.composition` (line 47), chosen from `CategoryTheory.exists_linear_scalarLocalization_category`
- `Sheaf.Paper.CompleteCoefficientDatum::AlgebraicGeometry.Scheme.adicBalanceHom` (line 202), chosen from `AlgebraicGeometry.Scheme.adicBalance_exists`
- `Sheaf.Paper.CompleteCoefficientDatum::AlgebraicGeometry.Scheme.adicTransitionComplex` (line 331), chosen from `AlgebraicGeometry.Scheme.adicTransitionComplex_exists`
- `Sheaf.Paper.CompleteCoefficientDatum::AlgebraicGeometry.Scheme.adicUnitHom` (line 495), chosen from `AlgebraicGeometry.Scheme.adicUnit_exists`
- `Sheaf.Paper.CompletionMap::AlgebraicGeometry.Scheme.adicCompletionTowerMap` (line 250), chosen from `AlgebraicGeometry.Scheme.adicCompletionTowerMap_exists`
- `Sheaf.Paper.CompletionMap::AlgebraicGeometry.Scheme.adicReductionAugmentation` (line 64), chosen from `AlgebraicGeometry.Scheme.adicReductionAugmentation_exists`
- `Sheaf.Paper.ExtendedLocalizationCech::SheafOfModules.LocalizationCech.unitMap` (line 190), chosen from `SheafOfModules.LocalizationCech.unitMap_existsUnique`
- `Sheaf.Paper.FiniteFieldFiber::WeilConjectures.FiniteFieldDatum.extensionEmbedding` (line 87), chosen from `FiniteField.exists_unique_subfield_of_closure`
- `Sheaf.Paper.FiniteFieldFiber::WeilConjectures.FiniteFieldDatum.extensionSubfield` (line 77), chosen from `FiniteField.exists_unique_subfield_of_closure`
- `Sheaf.Paper.IntegralReductionTowerWellDefined::WeilConjectures.integralTowerTransition` (line 208), chosen from `WeilConjectures.integralTowerMaps_existUnique`
- `Sheaf.Paper.IntegralReductionTowerWellDefined::WeilConjectures.integralTowerUnit` (line 201), chosen from `WeilConjectures.integralTowerMaps_existUnique`
- `Sheaf.Paper.IntrinsicKoszulCompletion::AlgebraicGeometry.Scheme.koszulConstantOne` (line 139), chosen from `AlgebraicGeometry.Scheme.koszulConstantOne_exists`
- `Sheaf.Paper.LisseAdicFiberFunctors::AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor` (line 144), chosen from `AlgebraicGeometry.Scheme.lisseAlgebraicFiberFunctor_exists`
- `Sheaf.Paper.LisseAdicSheaves::AlgebraicGeometry.Scheme.lisseCoefficientDiagramData` (line 527), chosen from `AlgebraicGeometry.Scheme.lisseCoefficientDiagram_exists`
- `Sheaf.Paper.ProjectionFormulaArrows::SheafOfModules.mixedTensorRepresentative` (line 290), chosen from `SheafOfModules.mixedTensorRepresentative_existsUnique`
- `Sheaf.Paper.RingedSiteIdeal::CategoryTheory.RingedSiteIdeal.extension` (line 172), chosen from `CategoryTheory.RingedSiteIdeal.existsUnique_extension`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback::SheafOfModules.ringedTopoiCanonicalDerivedTensorComparison` (line 752), chosen from `SheafOfModules.ringedTopoiCanonicalDerivedTensorPullback`
- `WeilConjectures.SmoothPurity.Defs::AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso` (line 106), chosen from `AlgebraicGeometry.ProEtale.CondensedRing.exists_normalizedSmoothPurityMaps`

| root | library | closure |
|---|---:|---:|
| Sheaf | 1084 | 195 |
| WeilConjectures | 177 | 90 |

| baseline | scope | closed | added | net | deleted | changed holed statements |
|---|---|---:|---:|---:|---:|---:|
| 889327369 (Queue at the start of stage 3) | library | 1680 | 746 | 934 | 734 | 18 |
| 660345513 (Application of proof-dependency imports) | library | 1676 | 744 | 932 | 680 | 18 |
| 660345513 (Application of proof-dependency imports) | closure | 1434 | 174 | 1260 | 604 | 1 |

No closure delta is quoted across 660345513: proof-dependency imports changed the reached set.

| landing class | count |
|---|---:|
| proved | 3812 |
| decomposed | 52 |
| moved | 4065 |
| pruned | 136 |
| other | 631 |

Per group: whole-library closed/added/net since stage 3; landing count is not progress. Closure progress is shown only after the imports baseline.

| group | landings | closed | added | net | moved share |
|---|---:|---:|---:|---:|---:|
| <unknown> | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| A2 | 133 | 131 | 100 | 31 | 70/133 (52.6%) |
| A3 | 135 | 131 | 85 | 46 | 59/135 (43.7%) |
| A4 | 84 | 89 | 54 | 35 | 41/84 (48.8%) |
| B2 | 136 | 142 | 88 | 54 | 55/136 (40.4%) |
| B3 | 158 | 165 | 94 | 71 | 65/158 (41.1%) |
| B4 | 77 | 79 | 50 | 29 | 35/77 (45.5%) |
| C1 | 151 | 155 | 114 | 41 | 76/151 (50.3%) |
| C2 | 128 | 123 | 86 | 37 | 59/128 (46.1%) |
| C3 | 123 | 131 | 82 | 49 | 57/123 (46.3%) |
| C4 | 67 | 67 | 35 | 32 | 23/67 (34.3%) |
| D2 | 149 | 147 | 92 | 55 | 63/149 (42.3%) |
| D3 | 118 | 135 | 72 | 63 | 52/118 (44.1%) |
| D4 | 75 | 72 | 48 | 24 | 29/75 (38.7%) |
| E1 | 165 | 198 | 107 | 91 | 82/165 (49.7%) |
| E2 | 128 | 123 | 85 | 38 | 60/128 (46.9%) |
| E3 | 121 | 136 | 95 | 41 | 59/121 (48.8%) |
| E4 | 55 | 62 | 27 | 35 | 19/55 (34.5%) |
| F1 | 152 | 157 | 108 | 49 | 72/152 (47.4%) |
| F2 | 153 | 165 | 99 | 66 | 62/153 (40.5%) |
| F3 | 104 | 104 | 63 | 41 | 43/104 (41.3%) |
| F4 | 67 | 65 | 43 | 22 | 29/67 (43.3%) |
| G1 | 143 | 142 | 114 | 28 | 76/143 (53.1%) |
| G2 | 142 | 139 | 91 | 48 | 63/142 (44.4%) |
| G3 | 104 | 106 | 66 | 40 | 45/104 (43.3%) |
| G4 | 60 | 51 | 31 | 20 | 20/60 (33.3%) |
| H1 | 141 | 140 | 107 | 33 | 75/141 (53.2%) |
| H2 | 115 | 111 | 92 | 19 | 66/115 (57.4%) |
| H3 | 123 | 138 | 100 | 38 | 69/123 (56.1%) |
| H4 | 61 | 60 | 42 | 18 | 31/61 (50.8%) |
| J1 | 126 | 134 | 75 | 59 | 53/126 (42.1%) |
| J2 | 107 | 109 | 70 | 39 | 51/107 (47.7%) |
| J3 | 121 | 127 | 77 | 50 | 54/121 (44.6%) |
| J4 | 62 | 53 | 40 | 13 | 27/62 (43.5%) |
| K1 | 122 | 139 | 89 | 50 | 61/122 (50.0%) |
| K2 | 123 | 121 | 84 | 37 | 65/123 (52.8%) |
| K3 | 109 | 109 | 77 | 32 | 56/109 (51.4%) |
| K4 | 66 | 53 | 35 | 18 | 24/66 (36.4%) |
| M1 | 142 | 147 | 92 | 55 | 65/142 (45.8%) |
| M2 | 131 | 135 | 104 | 31 | 70/131 (53.4%) |
| M3 | 109 | 111 | 72 | 39 | 52/109 (47.7%) |
| M4 | 46 | 50 | 24 | 26 | 17/46 (37.0%) |
| N1 | 137 | 138 | 108 | 30 | 74/137 (54.0%) |
| N2 | 130 | 119 | 78 | 41 | 57/130 (43.8%) |
| N3 | 89 | 84 | 65 | 19 | 45/89 (50.6%) |
| N4 | 57 | 56 | 48 | 8 | 29/57 (50.9%) |
| P1 | 120 | 140 | 93 | 47 | 67/120 (55.8%) |
| P2 | 133 | 125 | 82 | 43 | 56/133 (42.1%) |
| P3 | 103 | 95 | 81 | 14 | 52/103 (50.5%) |
| P4 | 54 | 50 | 39 | 11 | 26/54 (48.1%) |
| Q1 | 108 | 109 | 75 | 34 | 55/108 (50.9%) |
| Q2 | 105 | 108 | 80 | 28 | 53/105 (50.5%) |
| Q3 | 102 | 101 | 71 | 30 | 47/102 (46.1%) |
| Q4 | 48 | 51 | 27 | 24 | 21/48 (43.8%) |
| R1 | 126 | 129 | 98 | 31 | 67/126 (53.2%) |
| R2 | 123 | 131 | 75 | 56 | 52/123 (42.3%) |
| R3 | 98 | 95 | 65 | 30 | 42/98 (42.9%) |
| R4 | 60 | 51 | 41 | 10 | 26/60 (43.3%) |
| S1 | 124 | 126 | 106 | 20 | 69/124 (55.6%) |
| S2 | 125 | 130 | 102 | 28 | 66/125 (52.8%) |
| S3 | 106 | 101 | 63 | 38 | 48/106 (45.3%) |
| S4 | 48 | 46 | 35 | 11 | 24/48 (50.0%) |
| T1 | 111 | 114 | 82 | 32 | 56/111 (50.5%) |
| T2 | 133 | 155 | 97 | 58 | 64/133 (48.1%) |
| T3 | 102 | 97 | 77 | 20 | 53/102 (52.0%) |
| T4 | 68 | 60 | 38 | 22 | 24/68 (35.3%) |
| U1 | 126 | 129 | 92 | 37 | 62/126 (49.2%) |
| U2 | 136 | 130 | 92 | 38 | 63/136 (46.3%) |
| U3 | 97 | 100 | 69 | 31 | 49/97 (50.5%) |
| U4 | 52 | 46 | 40 | 6 | 28/52 (53.8%) |
| V1 | 115 | 107 | 85 | 22 | 55/115 (47.8%) |
| V2 | 126 | 123 | 90 | 33 | 62/126 (49.2%) |
| V3 | 107 | 111 | 75 | 36 | 56/107 (52.3%) |
| V4 | 50 | 44 | 38 | 6 | 25/50 (50.0%) |
| W2 | 114 | 119 | 78 | 41 | 54/114 (47.4%) |
| W3 | 85 | 86 | 58 | 28 | 40/85 (47.1%) |
| W4 | 49 | 43 | 36 | 7 | 27/49 (55.1%) |
| X2 | 121 | 118 | 95 | 23 | 64/121 (52.9%) |
| X3 | 101 | 96 | 62 | 34 | 43/101 (42.6%) |
| XR0d56945a24047e2a | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| XR1b27919aec52b018 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| XR33076d633fce5c89 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR701758115908ba19 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR70f81a388df1a824 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR916f3f6fae119923 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XR9e6d7250028f1981 | 1 | 1 | 1 | 0 | 1/1 (100.0%) |
| XRa0a656f89c54729e | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRa2c5451bd4aff80a | 1 | 0 | 2 | -2 | 0/1 (0.0%) |
| XRa3e07659d1a5d330 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XRaf46747ed5a82c85 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XRb0cc22400e136910 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRb44ad0154cf1285a | 1 | 3 | 0 | 3 | 0/1 (0.0%) |
| XRbb9b20b2b4a981ff | 2 | 0 | 0 | 0 | 0/2 (0.0%) |
| XRd4f549ddc0d8d578 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRd9718f5111d65eef | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XReedb48d351b955d4 | 1 | 0 | 0 | 0 | 0/1 (0.0%) |
| XRf51ccf77cd4e9fca | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| XRfef4bc449ceae451 | 1 | 1 | 0 | 1 | 0/1 (0.0%) |
| Y2 | 109 | 111 | 98 | 13 | 59/109 (54.1%) |
| Y3 | 104 | 91 | 56 | 35 | 45/104 (43.3%) |
| Z2 | 3 | 4 | 0 | 4 | 1/3 (33.3%) |
| launcher prover | 138 | 19 | 9 | 10 | 6/138 (4.3%) |

Nearest targets (claims from the scanned git tree; live leases may differ):

| module | distance | holes | group |
|---|---:|---:|---|
| WeilConjectures.PoincareDuality.Poincare | 0 | 1 | A4 |
| Sheaf.SmoothPurity.NormalizedWitness | 1 | 1 | — |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | 2 | 3 | B2 |
| WeilConjectures.ZetaFunction.TraceFormula | 2 | 1 | — |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | 3 | 1 | — |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | 3 | 1 | — |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | 3 | 1 | — |
| WeilConjectures.WeilSheaf.PoincareDuality | 3 | 1 | — |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | 4 | 1 | — |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | 4 | 1 | — |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | 4 | 1 | — |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | 4 | 2 | — |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension | 4 | 1 | — |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | 4 | 1 | — |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | 5 | 1 | — |
| Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion | 5 | 1 | — |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | 5 | 1 | — |
| Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence | 5 | 2 | — |
| Sheaf.AlgebraicGeometry.FundamentalGroup.OpenSubgroups | 5 | 1 | — |
| Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact | 5 | 1 | — |

Modules pruned since the imports baseline:

- `Sheaf.Algebra.Category.ModuleCat.FilteredColimitFlat`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullback`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison`
- `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomIsSheaf`
- `Sheaf.Algebra.Category.ModuleCat.TorSymmetry`
- `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels`
- `Sheaf.Algebra.ChangeIdealCompletion`
- `Sheaf.Algebra.CharpolyLocallyFree`
- `Sheaf.Algebra.ExtOneDirectSum`
- `Sheaf.Algebra.FiniteProjectiveTorAcyclic`
- `Sheaf.Algebra.FlatTorIdealCriterion`
- `Sheaf.Algebra.Homology.AcyclicLimitOrdinal`
- `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`
- `Sheaf.Algebra.Homology.BalancedDerivedTensorModel`
- `Sheaf.Algebra.Homology.BaseChangeRHomPerfect`
- `Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono`
- `Sheaf.Algebra.Homology.DerivedTensorActionNaturality`
- `Sheaf.Algebra.Homology.DerivedTensorLocalizationCohomology`
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`
- `Sheaf.Algebra.Homology.DerivedTensorTransitivity`
- `Sheaf.Algebra.Homology.DoubleComplexCokernelHomologyIso`
- `Sheaf.Algebra.Homology.FilteredColimitDerivedTensor`
- `Sheaf.Algebra.Homology.FilteredComplexZBDescription`
- `Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion`
- `Sheaf.Algebra.Homology.FreeResolutionSesSplit`
- `Sheaf.Algebra.Homology.FunctorialHomotopies`
- `Sheaf.Algebra.Homology.KFlatDerivedTensorAssociator`
- `Sheaf.Algebra.Homology.KInjectiveProducts`
- `Sheaf.Algebra.Homology.KernelShiftedMappingCone`
- `Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`
- `Sheaf.Algebra.Homology.LowerTruncationStepSES`
- `Sheaf.Algebra.Homology.MappingCylinderSplitFactorization`
- `Sheaf.Algebra.Homology.MittagLefflerLimitHomology`
- `Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap`
- `Sheaf.Algebra.Homology.RoosComplex`
- `Sheaf.Algebra.Homology.RowCycleLiftsToZigzag`
- `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange`
- `Sheaf.Algebra.Homology.SubcategoryRightResolution`
- `Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor`
- `Sheaf.Algebra.Homology.TorIndependentProjectiveComplexTensor`
- `Sheaf.Algebra.Homology.UnitEntrySplits`
- `Sheaf.Algebra.Homology.UpperTruncationStepSES`
- `Sheaf.Algebra.Homology.ZigzagModule`
- `Sheaf.Algebra.Homology.ZigzagModuleFunctorial`
- `Sheaf.Algebra.Homology.ZigzagToRowCokernel`
- `Sheaf.Algebra.Homology.ZigzagTrivialIfRowBoundary`
- `Sheaf.Algebra.LimitFinitePresentation`
- `Sheaf.Algebra.LocallyFreeCharpoly`
- `Sheaf.Algebra.LocallyFreeCharpolyProdMap`
- `Sheaf.Algebra.Module.GradedLocalizationExact`
- `Sheaf.Algebra.Module.LocalizedHomogeneousPiece`
- `Sheaf.Algebra.Module.ProjDegreeZeroLocalizationExact`
- `Sheaf.Algebra.Module.QuotientPrimaryComponentNoTorsion`
- `Sheaf.Algebra.Module.TorsionSubmoduleFlatBaseChangeIso`
- `Sheaf.Algebra.ProjectiveDimensionWellDefined`
- `Sheaf.Algebra.Schanuel`
- `Sheaf.Algebra.TorDimensionShiftNatural`
- `Sheaf.Algebra.TorDimensionShifting`
- `Sheaf.Algebra.TorOneSurjectiveChangeRings`
- `Sheaf.Algebra.TwoTermHomotopyEquivalenceDirectSum`
- `Sheaf.AlgebraicGeometry.AbelianStrictlyHenselianOpenGerm`
- `Sheaf.AlgebraicGeometry.AffineCohomologyLocalization`
- `Sheaf.AlgebraicGeometry.AffineComplementFiniteOnIntegralCurve`
- `Sheaf.AlgebraicGeometry.AffineDerivedConcentration`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteBaseChange`
- `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`
- `Sheaf.AlgebraicGeometry.AffineFibreProductTransition`
- `Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections`
- `Sheaf.AlgebraicGeometry.AffineKoszulHomAlternatingCech`
- `Sheaf.AlgebraicGeometry.AffineLocalAcyclicOpenRestriction`
- `Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal`
- `Sheaf.AlgebraicGeometry.AffinePseudoCoherentRHomQuasiCoherent`
- `Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree`
- `Sheaf.AlgebraicGeometry.AffineTruncationKernelFlat`
- `Sheaf.AlgebraicGeometry.Ample`
- `Sheaf.AlgebraicGeometry.AmpleFiniteAffineCover`
- `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine`
- `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine`
- `Sheaf.AlgebraicGeometry.AmpleIdealSection`
- `Sheaf.AlgebraicGeometry.AmpleOnReductionNoetherian`
- `Sheaf.AlgebraicGeometry.AmpleProjCanonicalMap`
- `Sheaf.AlgebraicGeometry.AmpleProjLocalChart`
- `Sheaf.AlgebraicGeometry.AmpleProjOpen`
- `Sheaf.AlgebraicGeometry.AmpleSeparated`
- `Sheaf.AlgebraicGeometry.AmpleSquareZeroThickening`
- `Sheaf.AlgebraicGeometry.AssociatedModule`
- `Sheaf.AlgebraicGeometry.AssociatedModuleHom`
- `Sheaf.AlgebraicGeometry.AssociatedModulePullback`
- `Sheaf.AlgebraicGeometry.AssociatedSectionsLocalize`
- `Sheaf.AlgebraicGeometry.BoundaryCechLocalLifts`
- `Sheaf.AlgebraicGeometry.BoundsFiberDegreesFieldPoints`
- `Sheaf.AlgebraicGeometry.CechH1Injective`
- `Sheaf.AlgebraicGeometry.CechH1MapNatural`
- `Sheaf.AlgebraicGeometry.ChowFiniteType`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFlatBaseChange`
- `Sheaf.AlgebraicGeometry.ClosedImmersionConormalFunctorial`
- `Sheaf.AlgebraicGeometry.ClosedPushforwardStalks`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage`
- `Sheaf.AlgebraicGeometry.ClosedSubsetProperUniversallyClosedImage`
- `Sheaf.AlgebraicGeometry.ClosedSubsetQcIdeal`
- `Sheaf.AlgebraicGeometry.CoherentFormalModuleIsomorphismLocal`
- `Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness`
- `Sheaf.AlgebraicGeometry.CoherentProjRepresentation`
- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`
- `Sheaf.AlgebraicGeometry.CommAlgebraSheaf`
- `Sheaf.AlgebraicGeometry.ComponentIntersectionsFinite`
- `Sheaf.AlgebraicGeometry.ConductorIdealRestriction`
- `Sheaf.AlgebraicGeometry.ConductorIdealZeroIntersection`
- `Sheaf.AlgebraicGeometry.ConductorSections`
- `Sheaf.AlgebraicGeometry.ConstantEtaleSheafShortExact`
- `Sheaf.AlgebraicGeometry.ConstantExtensionCover`
- `Sheaf.AlgebraicGeometry.ConstantModuleSheavesForgetColimits`
- `Sheaf.AlgebraicGeometry.ConstantPullbackCompositionCoherence`
- `Sheaf.AlgebraicGeometry.ConstantPullbackIdentityCoherence`
- `Sheaf.AlgebraicGeometry.ConstantRingModuleSheafEquivalence`
- `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk`
- `Sheaf.AlgebraicGeometry.ConstantSheafSetSectionsConnectedNatural`
- `Sheaf.AlgebraicGeometry.ConstantSubsheafGeneric`
- `Sheaf.AlgebraicGeometry.ConstructibleClosedGenericCriterion`
- `Sheaf.AlgebraicGeometry.ConstructibleModuleFiniteStalks`
- `Sheaf.AlgebraicGeometry.ConstructibleModuleSubobjectNoetherian`
- `Sheaf.AlgebraicGeometry.Curve.DenseIrreducibleOpens`
- `Sheaf.AlgebraicGeometry.Curve.DisjointOpenPrimeAssertions`
- `Sheaf.AlgebraicGeometry.Curve.PicAffineQuotient`
- `Sheaf.AlgebraicGeometry.Curve.ProperCohomology`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.Curve.SepClosedComparison`
- `Sheaf.AlgebraicGeometry.Curve.SepClosedComparisonCore`
- `Sheaf.AlgebraicGeometry.Curve.SepClosedComparisonCurve`
- `Sheaf.AlgebraicGeometry.DerivedBaseChangeMayerVietoris`
- `Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`
- `Sheaf.AlgebraicGeometry.DescendAffine`
- `Sheaf.AlgebraicGeometry.DescendQCOpenFGSubalgebra`
- `Sheaf.AlgebraicGeometry.DescendSurjective`
- `Sheaf.AlgebraicGeometry.DiagonalBaseChangeUpperShriek`
- `Sheaf.AlgebraicGeometry.DimOneQuasiProjective`
- `Sheaf.AlgebraicGeometry.DivisorClassCurve`
- `Sheaf.AlgebraicGeometry.DivisorModuleLocal`
- `Sheaf.AlgebraicGeometry.DvrFieldExtensionOrder`
- `Sheaf.AlgebraicGeometry.EtaleAlgebraFilteredColimitDescent`
- `Sheaf.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing`
- `Sheaf.AlgebraicGeometry.EtaleCechSectionwiseShortExact`
- `Sheaf.AlgebraicGeometry.EtaleCechVanishingCriterion`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyOverOpen`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZeroAux`
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleConstantRingModuleEquivalence`
- `Sheaf.AlgebraicGeometry.EtaleDirectedColimitDescent`
- `Sheaf.AlgebraicGeometry.EtaleEdgeMapBaseChange`
- `Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints`
- `Sheaf.AlgebraicGeometry.EtaleFinitePushforwardUnitEdgeCompatibility`
- `Sheaf.AlgebraicGeometry.EtaleGeometricFibreConstantSections`
- `Sheaf.AlgebraicGeometry.EtaleGeometricFibreInverseImageConstant`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageExact`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageSectionDescription`
- `Sheaf.AlgebraicGeometry.EtaleLocalFiniteAtPoint`
- `Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePoints`
- `Sheaf.AlgebraicGeometry.EtaleLocalFiniteMultiplePointsElementary`
- `Sheaf.AlgebraicGeometry.EtaleLocalizeUpstairs`
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `Sheaf.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`
- `Sheaf.AlgebraicGeometry.EtaleModulePullbackForgetNaturality`
- `Sheaf.AlgebraicGeometry.EtaleNeighbourhoodPrescribedResidueField`
- `Sheaf.AlgebraicGeometry.EtaleNormalComponents`
- `Sheaf.AlgebraicGeometry.EtaleOpenFpqcDescent`
- `Sheaf.AlgebraicGeometry.EtalePullbackForgetModules`
- `Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings`
- `Sheaf.AlgebraicGeometry.EtaleResidueTriples`
- `Sheaf.AlgebraicGeometry.EtaleSectionsSurjectiveOfCechH1`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageConstantSheaf`
- `Sheaf.AlgebraicGeometry.EtaleSetInverseImageExact`
- `Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`
- `Sheaf.AlgebraicGeometry.EtaleSheaves`
- `Sheaf.AlgebraicGeometry.EtaleShortExactLocalLift`
- `Sheaf.AlgebraicGeometry.EtaleSiteCechComplexComparison`
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
- `Sheaf.AlgebraicGeometry.EtaleSplitsOffIsolatedPoints`
- `Sheaf.AlgebraicGeometry.EtaleSplitsOffQuasiFinitePart`
- `Sheaf.AlgebraicGeometry.EtaleStratificationLocalGluing`
- `Sheaf.AlgebraicGeometry.EtaleSubsheafFinalOpen`
- `Sheaf.AlgebraicGeometry.EtaleUnderivedExchangeModuleLinear`
- `Sheaf.AlgebraicGeometry.EventuallyAffine`
- `Sheaf.AlgebraicGeometry.EventuallyClosedImmersion`
- `Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne`
- `Sheaf.AlgebraicGeometry.ExistsAmpleOfEnoughGloballyGenerated`
- `Sheaf.AlgebraicGeometry.ExistsAmpleOfReducedDimLEOne`
- `Sheaf.AlgebraicGeometry.ExtEvaluation`
- `Sheaf.AlgebraicGeometry.FiberDegreeBound`
- `Sheaf.AlgebraicGeometry.FibreProductPointResidueField`
- `Sheaf.AlgebraicGeometry.FieldDiscreteModules`
- `Sheaf.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion`
- `Sheaf.AlgebraicGeometry.FieldPointFactorsThroughImmersion`
- `Sheaf.AlgebraicGeometry.FilteredColimitLocalizationAtPrime`
- `Sheaf.AlgebraicGeometry.FindGloballyGenerated`
- `Sheaf.AlgebraicGeometry.FiniteAffineFibreSections`
- `Sheaf.AlgebraicGeometry.FiniteClopenOpenCoverSection`
- `Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen`
- `Sheaf.AlgebraicGeometry.FiniteDimensionalResidueFieldOfIsolatedFiberPoint`
- `Sheaf.AlgebraicGeometry.FiniteDiscreteSeparatedAffine`
- `Sheaf.AlgebraicGeometry.FiniteEtaleDescent`
- `Sheaf.AlgebraicGeometry.FiniteEtaleDescentData`
- `Sheaf.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTrace`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTraceExists`
- `Sheaf.AlgebraicGeometry.FiniteFiberDegreeBaseChange`
- `Sheaf.AlgebraicGeometry.FiniteFlatDualityEvaluation`
- `Sheaf.AlgebraicGeometry.FiniteIsolatedPointsOfFiniteType`
- `Sheaf.AlgebraicGeometry.FiniteLocallyConstantModuleValues`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDegreeLocallyConstant`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeDerivedHom`
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf`
- `Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints`
- `Sheaf.AlgebraicGeometry.FiniteOpenCoverDegreeSum`
- `Sheaf.AlgebraicGeometry.FinitePiecePersistence`
- `Sheaf.AlgebraicGeometry.FinitePushforwardLocallyFree`
- `Sheaf.AlgebraicGeometry.FiniteSectionsCover`
- `Sheaf.AlgebraicGeometry.FiniteSeparableMultiplicationEtale`
- `Sheaf.AlgebraicGeometry.FiniteTypeEtaleModuleStalk`
- `Sheaf.AlgebraicGeometry.FiniteUnramifiedEtaleLocal`
- `Sheaf.AlgebraicGeometry.FiniteUnramifiedOnePointClosed`
- `Sheaf.AlgebraicGeometry.FirstOrderThickeningBaseChange`
- `Sheaf.AlgebraicGeometry.FlatBoundedComplexDescent`
- `Sheaf.AlgebraicGeometry.FlatOfFpqcCover`
- `Sheaf.AlgebraicGeometry.FlatPrecomposePus`
- `Sheaf.AlgebraicGeometry.FlatUnramifiedFormallyEtale`
- `Sheaf.AlgebraicGeometry.FormallySmooth`
- `Sheaf.AlgebraicGeometry.FormallyUnramifiedConormal`
- `Sheaf.AlgebraicGeometry.FpqcAffineStandardRefinement`
- `Sheaf.AlgebraicGeometry.FpqcDescendQuasiCompact`
- `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend`
- `Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent`
- `Sheaf.AlgebraicGeometry.FpqcTensorSections`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleSite`
- `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`
- `Sheaf.AlgebraicGeometry.GeometricPointMorphismStalkBijection`
- `Sheaf.AlgebraicGeometry.GlobalGenerationNonvanishingCover`
- `Sheaf.AlgebraicGeometry.GlobalHomPullbackAdjunction`
- `Sheaf.AlgebraicGeometry.GlobalSectionsLeftExact`
- `Sheaf.AlgebraicGeometry.GlobalSectionsStalkComparison`
- `Sheaf.AlgebraicGeometry.GlueComponentLineBundles`
- `Sheaf.AlgebraicGeometry.GlueComponentReducedCoverSections`
- `Sheaf.AlgebraicGeometry.GlueComponentTransitionCocycle`
- `Sheaf.AlgebraicGeometry.GradedSheafStructures`
- `Sheaf.AlgebraicGeometry.GrothendieckExistenceEasy`
- `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Image`
- `Sheaf.AlgebraicGeometry.HenselianFinitePushforwardH1Lift`
- `Sheaf.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange`
- `Sheaf.AlgebraicGeometry.ImmersionAffineConstructiblePieces`
- `Sheaf.AlgebraicGeometry.ImmersionFiberDegreeOne`
- `Sheaf.AlgebraicGeometry.InjectiveEtaleConstantRingModule`
- `Sheaf.AlgebraicGeometry.InjectiveEtaleModuleCechH1`
- `Sheaf.AlgebraicGeometry.InjectiveModuleSheafH1`
- `Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres`
- `Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreChooseG`
- `Sheaf.AlgebraicGeometry.IntegralClosureFiniteFibreImageClopen`
- `Sheaf.AlgebraicGeometry.IntegralDimOneAmple`
- `Sheaf.AlgebraicGeometry.IntegralOverringJacobsonPower`
- `Sheaf.AlgebraicGeometry.InvertibleSectionRing`
- `Sheaf.AlgebraicGeometry.InvertibleTensorQcoherent`
- `Sheaf.AlgebraicGeometry.IsAffineOfFiniteClosedCover`
- `Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfDegreeOfEtaleCover`
- `Sheaf.AlgebraicGeometry.IsFiniteOfFpqcCover`
- `Sheaf.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf`
- `Sheaf.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange`
- `Sheaf.AlgebraicGeometry.IsSeparatedOfSurjectiveUniversallyClosed`
- `Sheaf.AlgebraicGeometry.IsolatedFibrePointBaseChange`
- `Sheaf.AlgebraicGeometry.KilledSheafModuleLift`
- `Sheaf.AlgebraicGeometry.LftOverFieldIsolatedPointResidueFinite`
- `Sheaf.AlgebraicGeometry.LimitContainedInConstructible`
- `Sheaf.AlgebraicGeometry.LocallyConstantFiniteValuesFiniteType`
- `Sheaf.AlgebraicGeometry.LocallyOfFinitePresentationFpqcDescent`
- `Sheaf.AlgebraicGeometry.MLSetsTowerLimitNonempty`
- `Sheaf.AlgebraicGeometry.MatchingObjectFibreProduct`
- `Sheaf.AlgebraicGeometry.ModuleAbelianInverseImageComparison`
- `Sheaf.AlgebraicGeometry.ModuleAcyclicCohomologyComparisonZero`
- `Sheaf.AlgebraicGeometry.ModuleAcyclicUnderlyingSections`
- `Sheaf.AlgebraicGeometry.ModuleCechVanishingBasis`
- `Sheaf.AlgebraicGeometry.ModuleCechVanishingCriterion`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyBoundary`
- `Sheaf.AlgebraicGeometry.ModuleInjectiveOpenCoverCechAcyclic`
- `Sheaf.AlgebraicGeometry.ModuleSectionsSurjectiveOfCechH1`
- `Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit`
- `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericConstancy`
- `Sheaf.AlgebraicGeometry.ModuleSubobjectGenericNeighbourhood`
- `Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`
- `Sheaf.AlgebraicGeometry.Modules.ModuleSkyscraperStalkAdjunction`
- `Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum`
- `Sheaf.AlgebraicGeometry.Modules.ResidueFiber`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcIntegralDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.FpqcOpenImmersionDescent`
- `Sheaf.AlgebraicGeometry.Morphisms.Projective`
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen`
- `Sheaf.AlgebraicGeometry.Morphisms.UnramifiedDescent`
- `Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope`
- `Sheaf.AlgebraicGeometry.NagataFixedBaseSeparatedStage`
- `Sheaf.AlgebraicGeometry.NormalGenericConstant`
- `Sheaf.AlgebraicGeometry.NormalizationProperties`
- `Sheaf.AlgebraicGeometry.OpenRestrictionPullbackUnit`
- `Sheaf.AlgebraicGeometry.PerfectDerivedTensorHom`
- `Sheaf.AlgebraicGeometry.PerfectGenerationOpenInduction`
- `Sheaf.AlgebraicGeometry.PicardH1RestrictionCompatibility`
- `Sheaf.AlgebraicGeometry.PicardLift`
- `Sheaf.AlgebraicGeometry.PopescuDelocalizeWeakLocalizationSmooth`
- `Sheaf.AlgebraicGeometry.PositiveTensorFamily`
- `Sheaf.AlgebraicGeometry.PresheafModuleStalkFilteredColimit`
- `Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent`
- `Sheaf.AlgebraicGeometry.ProjPolynomialTwistChart`
- `Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist`
- `Sheaf.AlgebraicGeometry.ProjStandardOpenBasis`
- `Sheaf.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism`
- `Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists`
- `Sheaf.AlgebraicGeometry.ProjectiveLineTwistMultiplication`
- `Sheaf.AlgebraicGeometry.ProjectiveSpace.KoszulResolution`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistGluedIdentification`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceTwistingSheafCharts`
- `Sheaf.AlgebraicGeometry.ProperBasic`
- `Sheaf.AlgebraicGeometry.ProperCoproduct`
- `Sheaf.AlgebraicGeometry.ProperDerivedDirectImageComposition`
- `Sheaf.AlgebraicGeometry.ProperGlobalSectionsFlatBaseChange`
- `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`
- `Sheaf.AlgebraicGeometry.PullbackIsoNsmulDevissage`
- `Sheaf.AlgebraicGeometry.PushforwardCoherentOnOpen`
- `Sheaf.AlgebraicGeometry.QcqsSchemeCofinalFiniteCoverings`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebra`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusion`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraChangeOfRings`
- `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraColimit`
- `Sheaf.AlgebraicGeometry.QuasiCoherentIsoOnAffineCover`
- `Sheaf.AlgebraicGeometry.QuasiCoherentMayerVietorisOpenCover`
- `Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections`
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`
- `Sheaf.AlgebraicGeometry.QuasicoherentSheafHom`
- `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`
- `Sheaf.AlgebraicGeometry.ReducedCurveNormalization`
- `Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism`
- `Sheaf.AlgebraicGeometry.RelativeSpecBaseChange`
- `Sheaf.AlgebraicGeometry.SchemeClopenIdempotent`
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`
- `Sheaf.AlgebraicGeometry.SchemeModulesFunctorialInjectiveEmbeddings`
- `Sheaf.AlgebraicGeometry.SchemeTheoreticUnion`
- `Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology`
- `Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing`
- `Sheaf.AlgebraicGeometry.SemiRepresentableObject`
- `Sheaf.AlgebraicGeometry.SemilocalDimOneConductor`
- `Sheaf.AlgebraicGeometry.SeparatedAffineCoverCriterion`
- `Sheaf.AlgebraicGeometry.SeparatedAffineFunctionFieldSurjective`
- `Sheaf.AlgebraicGeometry.SerreSectionModuleComparison`
- `Sheaf.AlgebraicGeometry.SerreSectionModuleFinite`
- `Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`
- `Sheaf.AlgebraicGeometry.Sites.FiniteEtaleCoproductSections`
- `Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`
- `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`
- `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`
- `Sheaf.AlgebraicGeometry.SmoothZeroDifferentialsAffineOpenEtale`
- `Sheaf.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant`
- `Sheaf.AlgebraicGeometry.SpecFieldPointResidueField`
- `Sheaf.AlgebraicGeometry.SpecFiniteProductFields`
- `Sheaf.AlgebraicGeometry.SpecStalkLimitAffineNeighbourhoods`
- `Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange`
- `Sheaf.AlgebraicGeometry.StandardFpqcQuotientTopology`
- `Sheaf.AlgebraicGeometry.StandardSmoothAffineDiagonalGenerators`
- `Sheaf.AlgebraicGeometry.SteinUniversallyClosedFactor`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianOpenSectionsStalk`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`
- `Sheaf.AlgebraicGeometry.TensorGeneratingSections`
- `Sheaf.AlgebraicGeometry.TensorGloballyGenerated`
- `Sheaf.AlgebraicGeometry.TensorSectionAffineOpen`
- `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickening`
- `Sheaf.AlgebraicGeometry.UniversalFirstOrderThickeningExists`
- `Sheaf.AlgebraicGeometry.UniversalThickeningAffineCase`
- `Sheaf.AlgebraicGeometry.UniversalThickeningFlatBaseChange`
- `Sheaf.AlgebraicGeometry.UniversalThickeningOpenPieces`
- `Sheaf.AlgebraicGeometry.UniversalThickeningOpenRestriction`
- `Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct`
- `Sheaf.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition`
- `Sheaf.AlgebraicGeometry.UnramifiedFibrePointIsolated`
- `Sheaf.AlgebraicGeometry.UnramifiedOverFieldDiscrete`
- `Sheaf.AlgebraicGeometry.UpperShriekRightAdjoint`
- `Sheaf.AlgebraicGeometry.Variety`
- `Sheaf.AlgebraicGeometry.ZariskiCohomologyLocallyZero`
- `Sheaf.AlgebraicGeometry.ZariskiExtensionByZeroAdjunction`
- `Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives`
- `Sheaf.AlgebraicGeometry.ZariskiUnitsRestriction`
- `Sheaf.AlgebraicGeometry.ZeroDimIntegralPoint`
- `Sheaf.AlgebraicGeometry.ZeroDimNoetherianAffine`
- `Sheaf.AlgebraicTopology.CoskeletalMapTrivialKan`
- `Sheaf.AlgebraicTopology.CoskeletonFreeHomologyComparison`
- `Sheaf.AlgebraicTopology.SetCechNerveFreeResolution`
- `Sheaf.CategoryTheory.Abelian.CompatibleNullHomotopyAssembly`
- `Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift`
- `Sheaf.CategoryTheory.Abelian.HorseshoeResolutions`
- `Sheaf.CategoryTheory.AdjunctionTransferFunctorialInjectives`
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
- `Sheaf.CategoryTheory.CommAlgebraSheafModule`
- `Sheaf.CategoryTheory.CoskeletonMatchingTuples`
- `Sheaf.CategoryTheory.DeltaFunctor`
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantInd`
- `Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantIndHomColimit`
- `Sheaf.CategoryTheory.DerivedCategory.ShiftIdentification`
- `Sheaf.CategoryTheory.DerivedCoupleExact`
- `Sheaf.CategoryTheory.DerivedFunctorInverts`
- `Sheaf.CategoryTheory.DiscreteModulesAbelian`
- `Sheaf.CategoryTheory.EdgeCollapse`
- `Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal`
- `Sheaf.CategoryTheory.EssentiallyConstantSplitting`
- `Sheaf.CategoryTheory.EssentiallyConstantSystem`
- `Sheaf.CategoryTheory.ExactCouple`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.CategoryTheory.FilteredColimitCategories`
- `Sheaf.CategoryTheory.FilteredHomotopySpectralSequence`
- `Sheaf.CategoryTheory.FilteredPageTwoModel`
- `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`
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
- `Sheaf.CategoryTheory.ImageFiltration`
- `Sheaf.CategoryTheory.InjectiveIffExtendsSubobjectGenerator`
- `Sheaf.CategoryTheory.InjectiveResolutionSESComplexes`
- `Sheaf.CategoryTheory.InjectiveSheafCechAcyclic`
- `Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact`
- `Sheaf.CategoryTheory.Limits.TowerTransitionEndomorphism`
- `Sheaf.CategoryTheory.LocalizationHomColimit`
- `Sheaf.CategoryTheory.MatchingObjectCoskeleton`
- `Sheaf.CategoryTheory.MittagLefflerExactSequence`
- `Sheaf.CategoryTheory.MittagLefflerLimitExact`
- `Sheaf.CategoryTheory.ModuleDirectedColimitUnderlyingSets`
- `Sheaf.CategoryTheory.OpcyclesTorSurjection`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.PresheafChangeOfRingsAdjunction`
- `Sheaf.CategoryTheory.PushoutShortExactSequence`
- `Sheaf.CategoryTheory.QuotientJShriek`
- `Sheaf.CategoryTheory.RightDerivedFunctorTruncationIso`
- `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`
- `Sheaf.CategoryTheory.RightLocalizationHomColimit`
- `Sheaf.CategoryTheory.SheafAlgebrasDirectedColimit`
- `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`
- `Sheaf.CategoryTheory.SiteCechComplex`
- `Sheaf.CategoryTheory.SiteCechMathlibComparison`
- `Sheaf.CategoryTheory.SiteCechVanishingCriterion`
- `Sheaf.CategoryTheory.SiteCohomologyPullback`
- `Sheaf.CategoryTheory.SiteContinuousPushforwardSheaf`
- `Sheaf.CategoryTheory.SiteCoveringsCommonRefinement`
- `Sheaf.CategoryTheory.SiteEquivalenceMorphismOfSites`
- `Sheaf.CategoryTheory.SiteEquivalenceMorphismTransport`
- `Sheaf.CategoryTheory.SiteExtensionByZeroPresheafAdjoint`
- `Sheaf.CategoryTheory.SiteFilteredColimitSections`
- `Sheaf.CategoryTheory.SiteInjectiveCechAcyclic`
- `Sheaf.CategoryTheory.SiteLerayDegenerate`
- `Sheaf.CategoryTheory.SiteMorphismComposition`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.CategoryTheory.SiteSesCechH1Surjective`
- `Sheaf.CategoryTheory.SiteSystemStrictification`
- `Sheaf.CategoryTheory.Sites.BinaryContractedProductPresentation`
- `Sheaf.CategoryTheory.Sites.CoherentContractedPowers`
- `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation`
- `Sheaf.CategoryTheory.Sites.CohomologySiteEquivalence`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtension`
- `Sheaf.CategoryTheory.Sites.EtaleTorsorPushoutExtension`
- `Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic`
- `Sheaf.CategoryTheory.Sites.SheafificationPlusTheorem`
- `Sheaf.CategoryTheory.Sites.SitePlusConstructionPresheaf`
- `Sheaf.CategoryTheory.Sites.TorsorExtensionPresentation`
- `Sheaf.CategoryTheory.Sites.TorsorExtensionPushforward`
- `Sheaf.CategoryTheory.Sites.TorsorH1BoundaryRepresentative`
- `Sheaf.CategoryTheory.Sites.TorsorH1Functoriality`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtension`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerExtensionPresentation`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedPowerTorsor`
- `Sheaf.CategoryTheory.Sites.ZariskiContractedProductPresentation`
- `Sheaf.CategoryTheory.Sites.ZariskiExtTorsor`
- `Sheaf.CategoryTheory.Sites.ZariskiTorsorExtensionPushout`
- `Sheaf.CategoryTheory.SpecialCocontinuousCoverings`
- `Sheaf.CategoryTheory.SpectralSequenceComparison`
- `Sheaf.CategoryTheory.SpectralSequencePageInduction`
- `Sheaf.CategoryTheory.TowerSplitEnvelope`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`
- `Sheaf.CategoryTheory.Triangulated.TriangleMorphismExtension`
- `Sheaf.CategoryTheory.TruncatedCoskeletonFiniteLimits`
- `Sheaf.CategoryTheory.TruncationCoupleExact`
- `Sheaf.CategoryTheory.TruncationDescends`
- `Sheaf.FieldTheory.ExistsPBasis`
- `Sheaf.FieldTheory.FiniteGaloisReceivingSeparableExtensions`
- `Sheaf.FieldTheory.FinitePurelyInseparableScalarDescent`
- `Sheaf.FieldTheory.FiniteSeparableTensorFieldReduced`
- `Sheaf.FieldTheory.FinitelyGeneratedFieldCompleteIntersectionModel`
- `Sheaf.FieldTheory.GeometricallyReducedExtensionSeparable`
- `Sheaf.FieldTheory.IntersectionSubfieldsDifferentials`
- `Sheaf.FieldTheory.IntersectionSubfieldsSubspace`
- `Sheaf.FieldTheory.MakeSeparable`
- `Sheaf.FieldTheory.MakeSeparablyGenerated`
- `Sheaf.FieldTheory.NormalExtensionFixedField`
- `Sheaf.FieldTheory.PBasisDifferentialsBasis`
- `Sheaf.FieldTheory.PBasisExtension`
- `Sheaf.FieldTheory.PIndependentDifferentialsIndependent`
- `Sheaf.FieldTheory.PthRootsExtensionDegree`
- `Sheaf.FieldTheory.PurelyInseparableDegreePIntermediate`
- `Sheaf.FieldTheory.PurelyInseparablePthRootTower`
- `Sheaf.FieldTheory.SeparableExtension`
- `Sheaf.FieldTheory.SeparableRootPthPower`
- `Sheaf.FieldTheory.SeparableSplitPurelyInseparableResidueFields`
- `Sheaf.FieldTheory.SeparableTensorPurelyInseparable`
- `Sheaf.FieldTheory.SeparablyGeneratedDifferentialsDimension`
- `Sheaf.FieldTheory.SeparablyGeneratedSeparable`
- `Sheaf.FieldTheory.SeparablyGeneratedTensorReduced`
- `Sheaf.FieldTheory.SeparatingTranscendenceBasisFiniteSubextension`
- `Sheaf.FieldTheory.TensorFieldExtensionGaloisInvariants`
- `Sheaf.GroupTheory.GroupAlgebraFunctorialInjectiveEmbeddings`
- `Sheaf.LinearAlgebra.IdempotentEndomorphismCharpolyField`
- `Sheaf.LinearAlgebra.IdempotentImageBaseChange`
- `Sheaf.LinearAlgebra.Matrix.CauchyBinet`
- `Sheaf.LinearAlgebra.Matrix.LeftInverseMinors`
- `Sheaf.LinearAlgebra.NonzeroMaximalMinorOfInjective`
- `Sheaf.LinearAlgebra.SplitExtensionFreePresentation`
- `Sheaf.LinearAlgebra.SymmetricAlgebra.DegreeExact`
- `Sheaf.LinearAlgebra.SymmetricAlgebra.Graded`
- `Sheaf.LinearAlgebra.TensorProduct.ColimitVaryingRings`
- `Sheaf.LinearAlgebra.TriangularChangeOfBasis`
- `Sheaf.Paper.AffineProjectiveComplexDerivedHom`
- `Sheaf.Paper.ArtinianIdealLengthOneFiltration`
- `Sheaf.Paper.BoundaryCechCompatibility`
- `Sheaf.Paper.BoundaryCechInjectiveMiddle`
- `Sheaf.Paper.BoundaryDerivationSquareZero`
- `Sheaf.Paper.CartanEilenbergLeftExactCohomology`
- `Sheaf.Paper.CechNerveFreeHomology`
- `Sheaf.Paper.ColimitSitesInjectiveSystem`
- `Sheaf.Paper.ColimitSurjectiveRingMap`
- `Sheaf.Paper.ConstantSheafOpenMaps`
- `Sheaf.Paper.CyclicExtensionCocycle`
- `Sheaf.Paper.DerivationExtendsFiniteType`
- `Sheaf.Paper.DirectImageSplitCoverProduct`
- `Sheaf.Paper.DirectedColimitBaseChangeElementwise`
- `Sheaf.Paper.EtaleFiniteDataDescent`
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`
- `Sheaf.Paper.EtaleRestrictionPullbackUnit`
- `Sheaf.Paper.EtaleStandardCoverCech`
- `Sheaf.Paper.FiniteEtaleEtaleLocalSplit`
- `Sheaf.Paper.FiniteHypercoverDescent`
- `Sheaf.Paper.FiniteSplitEtaleHypercover`
- `Sheaf.Paper.FiniteSplitHypercoverRefinement`
- `Sheaf.Paper.FlatFibresIrreducible`
- `Sheaf.Paper.FlatLocalCriterionNonzerodivisor`
- `Sheaf.Paper.FreeCechComplexExact`
- `Sheaf.Paper.FreeComplexMapsToResolution`
- `Sheaf.Paper.GabberZariskiEtaleRestrictionInjective`
- `Sheaf.Paper.HypercoverCohomology`
- `Sheaf.Paper.HypercoverCohomologyColimit`
- `Sheaf.Paper.HypercoverFreeResolution`
- `Sheaf.Paper.ImagePresheafSheafificationIso`
- `Sheaf.Paper.IntegralClosureFiniteFibrePartLocalization`
- `Sheaf.Paper.InverseImageExtensionByEmptyConstant`
- `Sheaf.Paper.InverseImageFreeEtaleModule`
- `Sheaf.Paper.InverseImageStalkGerm`
- `Sheaf.Paper.KoszulComplex`
- `Sheaf.Paper.KoszulDifferential`
- `Sheaf.Paper.KoszulDifferentialSquareZero`
- `Sheaf.Paper.PlusConstructionFunctorial`
- `Sheaf.Paper.PolynomialIdealCoefficientsMonomial`
- `Sheaf.Paper.PowerSetComplexContractible`
- `Sheaf.Paper.ReducedSourceFactors`
- `Sheaf.Paper.RelativeGlobalCompleteIntersection`
- `Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation`
- `Sheaf.Paper.SectionsOverQuasiCompactOpen`
- `Sheaf.Paper.SeparableResidueCotangentInjective`
- `Sheaf.Paper.SetsEtaleInverseImageConstantBaseChange`
- `Sheaf.Paper.SheavesKilledByNZmodModules`
- `Sheaf.Paper.SiteCoveringIsomorphicFamily`
- `Sheaf.Paper.SiteCoveringMorphismsSameH0Map`
- `Sheaf.Paper.SiteHigherDirectImageSheafifiedPresheaf`
- `Sheaf.Paper.SitePlusInjectiveSeparated`
- `Sheaf.Paper.SitePlusOfSeparatedIsSheaf`
- `Sheaf.Paper.SitePlusOfSheafIso`
- `Sheaf.Paper.SitePlusSeparated`
- `Sheaf.Paper.SiteSheafificationSectionsLocal`
- `Sheaf.Paper.SmoothAtMaximalIdeal`
- `Sheaf.Paper.SmoothRetractRelativeGlobalCompleteIntersection`
- `Sheaf.Paper.StrictlyHenselianEtaleAcyclic`
- `Sheaf.Paper.TorLongExactFirstVariable`
- `Sheaf.Paper.TorsionModuleFlatBaseChangeIso`
- `Sheaf.Paper.TrivialKanHomotopyEquivalence`
- `Sheaf.Paper.WeilPbcNormalizationInResidueFieldExtension`
- `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`
- `Sheaf.Paper.ZariskiH0ProperHenselianPair`
- `Sheaf.Paper.ZeroDimensionalCohomology`
- `Sheaf.RepresentationTheory.CoinducedContinuousAcyclic`
- `Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding`
- `Sheaf.RepresentationTheory.CoinducedHomotopyContinuous`
- `Sheaf.RepresentationTheory.CoinducedHomotopyIdentity`
- `Sheaf.RepresentationTheory.ContinuousCochainsDerivedInvariants`
- `Sheaf.RepresentationTheory.ContinuousCochainsShortExact`
- `Sheaf.RepresentationTheory.DiscreteContinuousCohomology`
- `Sheaf.RepresentationTheory.DiscreteContinuousFunctorialInjectives`
- `Sheaf.RepresentationTheory.DiscreteContinuousInjectives`
- `Sheaf.RepresentationTheory.DiscreteContinuousRep`
- `Sheaf.RepresentationTheory.DiscreteRep`
- `Sheaf.RepresentationTheory.OpenStabilizerAdjunction`
- `Sheaf.RepresentationTheory.SylowModuleFiltration`
- `Sheaf.RingTheory.AffineBasicSetDifference`
- `Sheaf.RingTheory.AffineBasicSetsDisjointRefinement`
- `Sheaf.RingTheory.AnalyticallyUnramified`
- `Sheaf.RingTheory.AnnihilatorAssociatedPrimes`
- `Sheaf.RingTheory.AnnihilatorAssociatedPrimesExactSequence`
- `Sheaf.RingTheory.AnnihilatorElementFlatBaseChange`
- `Sheaf.RingTheory.AnnihilatorLocalizationAway`
- `Sheaf.RingTheory.ArtinianLocalEssentiallyFiniteTypeResidue`
- `Sheaf.RingTheory.AssociatedGradedRing`
- `Sheaf.RingTheory.AssociatedPrimeLocalizeAtPrime`
- `Sheaf.RingTheory.AssociatedPrimePowerQuotient`
- `Sheaf.RingTheory.BijectiveQuotientMapPowOfFlat`
- `Sheaf.RingTheory.CohenRing`
- `Sheaf.RingTheory.ColimitCategoryFpAlgebras`
- `Sheaf.RingTheory.ColimitFinitelyPresentedAlgebras`
- `Sheaf.RingTheory.CompletedModuleAssociatedGradedGenerators`
- `Sheaf.RingTheory.CompletionFiniteQuotient`
- `Sheaf.RingTheory.ConormalGeneratorsGlobalCompleteIntersection`
- `Sheaf.RingTheory.DVRValuationRingCharacterization`
- `Sheaf.RingTheory.DirectedUnionSubringsFlatModule`
- `Sheaf.RingTheory.EtaleFiniteFactorDecomposition`
- `Sheaf.RingTheory.EtaleLiftCoprimeFactorization`
- `Sheaf.RingTheory.EtaleRetractionFiniteProductLocal`
- `Sheaf.RingTheory.EtaleRetractionFiniteTypeSplitting`
- `Sheaf.RingTheory.EtaleRingMapConormalCriterion`
- `Sheaf.RingTheory.ExistsNegativeValuationOfTensorSurjective`
- `Sheaf.RingTheory.FiniteGabberPolynomial`
- `Sheaf.RingTheory.FiniteHomogeneousGenerators`
- `Sheaf.RingTheory.FiniteIffFormalGlueing`
- `Sheaf.RingTheory.FiniteIntegralConductor`
- `Sheaf.RingTheory.FiniteLengthGlobalSubmodule`
- `Sheaf.RingTheory.FiniteMaximalsOverElement`
- `Sheaf.RingTheory.FinitePresentationAndFlatOfFiniteFreeStandardCover`
- `Sheaf.RingTheory.FiniteProjectiveOfStandardCover`
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`
- `Sheaf.RingTheory.FiniteQuotientComponentQuasiFinite`
- `Sheaf.RingTheory.FiniteSeparableFibersOfEtaleColimit`
- `Sheaf.RingTheory.FractionalPrincipalQuotientAssociatedPrimes`
- `Sheaf.RingTheory.GradedAlgebra.ShortExactGradedComponent`
- `Sheaf.RingTheory.GradedKernelFinite`
- `Sheaf.RingTheory.GradedNakayamaFree`
- `Sheaf.RingTheory.GradedNakayamaGeneration`
- `Sheaf.RingTheory.GradedPrimeAvoidance`
- `Sheaf.RingTheory.GradedSubmoduleFinite`
- `Sheaf.RingTheory.GradedSyzygy`
- `Sheaf.RingTheory.HenselianFiniteEtaleEquivalence`
- `Sheaf.RingTheory.HenselianFiniteTypeProductDecomposition`
- `Sheaf.RingTheory.HenselianLocalRootLifting`
- `Sheaf.RingTheory.HenselianOfEtaleSectionLifting`
- `Sheaf.RingTheory.ImprovePresentationSmoothConormalFree`
- `Sheaf.RingTheory.IndStandardSmooth`
- `Sheaf.RingTheory.IntegralIdempotentAnnihilatingPolynomial`
- `Sheaf.RingTheory.IsolatedPrimeResidueFinite`
- `Sheaf.RingTheory.JacobianPresentationLift`
- `Sheaf.RingTheory.JacobsonDenominatorFunctionField`
- `Sheaf.RingTheory.KaehlerDifferentialsModPowerIdeal`
- `Sheaf.RingTheory.KrullAkizukiNoetherian`
- `Sheaf.RingTheory.KrullIntersectionLocalization`
- `Sheaf.RingTheory.LiftMonicCoprimeFactorizationEtale`
- `Sheaf.RingTheory.LocalCompleteIntersectionFieldChange`
- `Sheaf.RingTheory.LocalDimensionZeroHenselian`
- `Sheaf.RingTheory.LocalDomainDimOnePrincipalLocalization`
- `Sheaf.RingTheory.MinimalGradedPresentation`
- `Sheaf.RingTheory.MinimalPresentationTor`
- `Sheaf.RingTheory.ModuleLocalizationFilteredColimit`
- `Sheaf.RingTheory.MvPolynomial.TwoVariableSyzygy`
- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfReducedStronglyTranscendental`
- `Sheaf.RingTheory.NotQuasiFiniteAtPrimeOfStronglyTranscendental`
- `Sheaf.RingTheory.PolynomialDistinctLinearCRT`
- `Sheaf.RingTheory.PopescuEnlargeSolutionModulo`
- `Sheaf.RingTheory.PopescuLiftOnce`
- `Sheaf.RingTheory.PopescuLiftTwice`
- `Sheaf.RingTheory.PowerSeriesFieldCohenFsAdic`
- `Sheaf.RingTheory.PowerSeriesOntoCompletion`
- `Sheaf.RingTheory.PrescribedResidueBasisSpreads`
- `Sheaf.RingTheory.PresentationsHomotopyEquivalent`
- `Sheaf.RingTheory.PrincipalMaximalDimOneRegular`
- `Sheaf.RingTheory.ProjectiveDimensionSESKernel`
- `Sheaf.RingTheory.PseudoCoherentBoundedFiniteFreeModel`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePermanence`
- `Sheaf.RingTheory.QuasiFiniteAtPrimePrincipalLocalization`
- `Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen`
- `Sheaf.RingTheory.QuasiFiniteLocusOpen`
- `Sheaf.RingTheory.QuasiFiniteMonogenicIntegralClosure`
- `Sheaf.RingTheory.RadicialPrimeUniqueDegreeP`
- `Sheaf.RingTheory.ReducedIdealsZeroIntersection`
- `Sheaf.RingTheory.RegularSequenceShortExactSequence`
- `Sheaf.RingTheory.RegularSequenceSwapTwo`
- `Sheaf.RingTheory.RootLiftingEtaleRetraction`
- `Sheaf.RingTheory.SemilocalDedekindDvrReduction`
- `Sheaf.RingTheory.SemilocalNormalizationDimOne`
- `Sheaf.RingTheory.SeparablePolynomialQuotientReduced`
- `Sheaf.RingTheory.SeparateImageClosedFromClosed`
- `Sheaf.RingTheory.SimpleFiltration`
- `Sheaf.RingTheory.SplitInjectionAfterCompletion`
- `Sheaf.RingTheory.StandardSmoothDimensionAtPoints`
- `Sheaf.RingTheory.SymmetricAlgebraQuotientModule`
- `Sheaf.RingTheory.SymmetricProjectivePresentationConormal`
- `Sheaf.RingTheory.TensorFiniteTypeLimit`
- `Sheaf.RingTheory.TorStrictlyProZero`
- `Sheaf.RingTheory.UniversalFirstOrderThickening`
- `Sheaf.RingTheory.ValuationRingNormal`
- `Sheaf.RingTheory.ZariskiPairFlatIntegralIsomorphism`
- `Sheaf.RingTheory.ZariskiPairRankOnePropagation`
- `Sheaf.RingTheory.ZariskisMainAway`
- `Sheaf.Topology.AbelianCohomologyDeltaFunctor`
- `Sheaf.Topology.BasisSheafSectionsGerms`
- `Sheaf.Topology.ClosedPushforwardBoundaryNaturality`
- `Sheaf.Topology.ClosedPushforwardConstantPresheaf`
- `Sheaf.Topology.ClosedPushforwardConstantRestriction`
- `Sheaf.Topology.ClosedPushforwardConstantStalks`
- `Sheaf.Topology.ContinuousOpenNormalStabilizer`
- `Sheaf.Topology.ExistsUniqueIsGenericPointOfFinite`
- `Sheaf.Topology.FilteredInjectiveCechAcyclic`
- `Sheaf.Topology.InverseImageClosedPushforwardConstant`
- `Sheaf.Topology.InverseImageOperationExt`
- `Sheaf.Topology.InverseImagePresheafModule`
- `Sheaf.Topology.LocallyConstantGermEvaluation`
- `Sheaf.Topology.LocallyConstantMapsPresheaf`
- `Sheaf.Topology.LocallyConstantMapsSheaf`
- `Sheaf.Topology.NoetherianCohomologyDimOne`
- `Sheaf.Topology.SetsExtensionByEmpty`
- `Sheaf.Topology.SetsExtensionByEmptyAdjunction`
- `Sheaf.Topology.SetsInverseImageComposition`
- `Sheaf.Topology.SheafBasisSurjection`
- `Sheaf.Topology.SheafCokernelLocalImage`
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
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.AlgClosedExtension`
- `WeilConjectures.SixFunctors.Finite.GlobalSections`

Scanner limitations: macro-generated declarations, elaborated anonymous/private names, and tactic dependencies cannot be recovered from source. Synthetic names are source keys, not elaborated names.

Diagnostics:

- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.ContainsZero>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderRetracts>
- WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat: duplicate source declaration: <anonymous:instance : (quasiIso A (.up ℤ)).kFlat.IsStableUnderShift ℤ>
