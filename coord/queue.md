# Work queue

787 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (1)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `new-proetale-derived-module-pullback-monoidal` | - | none |

## Stage 2: nodes to state (31)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `sk-d-six` | 1 | state | 42 |
| `sk-def-sf-orientation` | 2 | state | 17 |
| `def-sf-pairing` | 1 | state | 3 |
| `sk-def-sp-trace` | 2 | state | 2 |
| `thm-sf-kunneth-relative` | 1 | state | 37 |
| `lem-pur-vector-integration-site-comparison` | 1 | state | 36 |
| `lem-pur-adic-purity-scalar-naturality` | 1 | state | 33 |
| `det-sp-tower-gluing` | 1 | state | 15 |
| `sk-thm-sf-kunneth-relative` | 1 | state | 12 |
| `sk-thm-sf-tensor-hom` | 1 | state | 4 |
| `lem-tw-lisse-rational-realization` | 1 | state | 3 |
| `det-prop-diagonal-tower-coefficients` | 1 | state | 2 |
| `lem-pur-system-level-projection-formula-coherence` | 1 | state | 2 |
| `lem-sf-open-external-tensor-normalization` | 1 | state | 2 |
| `prop-sf-pf-coherence` | 2 | state | 2 |
| `cor-sf-duality-pullback` | 1 | state | 1 |
| `lem-coef-cartesian-section-adjoint-mates` | 1 | state | 1 |
| `lem-trf-derived-evaluation-canonical-map` | 1 | state | 1 |
| `det-sp-p1-trace` | 1 | state | 0 |
| `lem-pod-hom-chain-counit-formula` | 1 | state | 0 |
| `lem-pur-adic-projection-shift-coherence` | 1 | state | 0 |
| `lem-pur-condensed-exceptional-reconstruction` | 1 | state | 0 |
| `lem-pur-weil-basechange-semilinear-pasting` | 1 | state | 0 |
| `lem-pur-weil-semilinear-exchange-reindexing` | 1 | state | 0 |
| `lem-trf-source-hyperext-module-target` | 1 | state | 0 |
| `lem-wf-constant-twist-coefficient-comparison` | 1 | state | 0 |
| `lem-zl-proper-unit-condensed-realization` | 1 | state | 0 |
| `thm-pur-vector-bundle-thom` | 1 | state | 0 |
| `lem-coef-finite-scalar-mate-realization` | 2 | state | 0 |
| `lem-zl-compact-support-realization-factor-normalization` | 2 | state | 0 |
| `nt-target-poincare-isiso` | 2 | state | 0 |

Not open yet: 301 nodes that below a finished node, not needed, 85 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (596)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.RelativeProjExists` | 10 | 1 | repair | route |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 10 | 1 | repair | route |
| `Sheaf.Paper.SfHomTriangulated` | 8 | 1 | repair | route |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 7 | 3 | repair | route |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | - | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | disputed | route |
| `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction` | 8 | 1 | disputed | 6 |
| `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian` | 1 | 2 | proof | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal` | 2 | 10 | proof | route |
| `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` | 2 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` | 3 | 3 | proof | route |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | 3 | 1 | proof | route |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 6 | proof | route |
| `Sheaf.Paper.IntegralHomReduction` | 3 | 1 | proof | route |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | route |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | 3 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` | 3 | 2 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 3 | 10 | proof | route |
| `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients` | 4 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction` | 4 | 2 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus` | 4 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedDerivedRestriction` | 4 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedKoszulCompletionReflector` | 4 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 6 | proof | route |
| `Sheaf.Paper.AdicCoefficientDatum` | 4 | 5 | proof | route |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 4 | 24 | proof | route |
| `Sheaf.Paper.ProperBaseChangeRational` | 4 | 6 | proof | route |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleAffineContinuity` | 5 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedCechCompletionUnitIdempotence` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompletedAdicCoefficientDatum` | 5 | 9 | proof | route |
| `Sheaf.Paper.CompletedKoszulQuotientComparison` | 5 | 1 | proof | route |
| `Sheaf.Paper.CompletedTowerPullback` | 5 | 12 | proof | route |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | 5 | 1 | proof | route |
| `Sheaf.Paper.LisseNormalizedTowerLocalModels` | 5 | 1 | proof | route |
| `Sheaf.Paper.NormalizedTowerCommonLisseStrata` | 5 | 1 | proof | route |
| `Sheaf.Paper.StrictPerfectCoefficientPackage` | 5 | 9 | proof | route |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | 5 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | 5 | 2 | proof | route |
| `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel` | 6 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedSitePerfectDuality` | 6 | 1 | proof | route |
| `Sheaf.Paper.CoefficientHomAugmentation` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteCoefficientHomChange` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence` | 6 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | 6 | 5 | proof | route |
| `Sheaf.Paper.FiniteProperLocalizing` | 6 | 3 | proof | route |
| `Sheaf.Paper.IntegralOperationsScalarExtension` | 6 | 1 | proof | route |
| `Sheaf.Paper.PbcCompletedPullbackActual` | 6 | 3 | proof | route |
| `Sheaf.Paper.RingedModelCurryingCoherence` | 6 | 1 | proof | route |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | 6 | 1 | proof | route |
| `Sheaf.SixFunctors.DetSfCompCompositionBaseChange` | 6 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` | 7 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback` | 7 | 1 | proof | route |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 7 | 11 | proof | route |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | 7 | 6 | proof | route |
| `Sheaf.Paper.FiniteConstructibleHom` | 7 | 2 | proof | route |
| `Sheaf.Paper.IntegralTensorProduct` | 7 | 1 | proof | route |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | 7 | 1 | proof | route |
| `Sheaf.Paper.RefinementBoundaryVanishing` | 7 | 1 | proof | route |
| `Sheaf.Paper.RingComplexGodementCech` | 7 | 1 | proof | route |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | 7 | 2 | proof | route |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | 7 | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleHomThickLocus` | 7 | 2 | proof | route |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | 7 | 1 | proof | route |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData` | 7 | 1 | proof | route |
| `WeilConjectures.SixFunctors.Etale.Derived.CompactificationUpperShriek` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.FixSiteOpenExchangeSheaf` | 8 | 1 | proof | route |
| `Sheaf.Paper.BrownExceptionalAdjoint` | 8 | 1 | proof | route |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | 8 | 1 | proof | route |
| `Sheaf.Paper.DiagonalTowerSystem` | 8 | 1 | proof | route |
| `Sheaf.Paper.DualityPairing` | 8 | 2 | proof | route |
| `Sheaf.Paper.EtaleDerivedScalarTensor` | 8 | 1 | proof | route |
| `Sheaf.Paper.FiniteCompactSupportScalarTransport` | 8 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeHomComparison` | 8 | 1 | proof | route |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | 8 | 1 | proof | route |
| `Sheaf.Paper.IntegralLocalizingProperBaseChange` | 8 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | 8 | 1 | proof | route |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | 8 | 1 | proof | route |
| `Sheaf.Paper.StratumAmbientHom` | 8 | 2 | proof | route |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates` | 8 | 1 | proof | route |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifUpperShriek` | 8 | 1 | proof | route |
| `Sheaf.Algebra.Homology.SignedDoubleHomCone` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison` | 9 | 3 | proof | route |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization` | 9 | 1 | proof | route |
| `Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint` | 9 | 3 | proof | route |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | 9 | 1 | proof | route |
| `Sheaf.Paper.DerivedDirectImageOpenCoherence` | 9 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | 9 | 1 | proof | route |
| `Sheaf.Paper.IntegralStratumHomFormula` | 9 | 2 | proof | route |
| `Sheaf.Paper.PurEtaleScalarMateProjection` | 9 | 2 | proof | route |
| `Sheaf.Paper.SemilinearOperationsExistence` | 9 | 1 | proof | route |
| `Sheaf.Paper.SemilinearSystemsExistence` | 9 | 1 | proof | route |
| `Sheaf.Paper.UnboundedProperOpenInterchange` | 9 | 1 | proof | route |
| `Sheaf.Paper.UniformConstructibleExtRational` | 9 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension` | 9 | 1 | proof | route |
| `WeilConjectures.WeilSheaf.PoincareDualityLisse` | 9 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose` | 10 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProperHeartBoundRational` | 10 | 2 | proof | route |
| `Sheaf.CategoryTheory.SystemLevelLeftExtension` | 10 | 2 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullbackBase` | 11 | 1 | proof | route |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | 11 | 4 | proof | route |
| `Sheaf.Paper.IntegralProperReductionModel` | 11 | 1 | proof | route |
| `Sheaf.SixFunctors.GeoCartierCoeffExtension` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` | 12 | 11 | proof | route |
| `Sheaf.Paper.AdicReductionCohomologySequence` | 12 | 1 | proof | route |
| `Sheaf.Paper.AdicSuppliedModelFlatCriterion` | 12 | 1 | proof | route |
| `Sheaf.Paper.AdicTorFlatCriterion` | 12 | 1 | proof | route |
| `Sheaf.Paper.ProperHeartBoundTorsion` | 12 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | 14 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AffineTraceLineLocalization` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange` | 16 | 1 | proof | route |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | - | 1 | proof | route |
| `Sheaf.Algebra.Homology.ScalarInternalHomAdjunction` | 3 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.CompletedCondensedCoefficients` | 3 | 4 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 6 | proof | 1 |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 4 | proof | 1 |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.ExceptionalInverseImageExistence` | 4 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralProperBaseChange` | 4 | 1 | proof | 1 |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | 4 | 1 | proof | 1 |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | 4 | 3 | proof | 1 |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.CartesianCoefficients` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.CartesianCoefficientsFiniteFree` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.FiniteLevelProEtaleBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 6 | 12 | proof | 1 |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | 6 | 3 | proof | 1 |
| `Sheaf.Paper.ExceptionalAdjointAdmissibility` | 6 | 1 | proof | 1 |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 21 | proof | 1 |
| `Sheaf.Paper.IntegralOperationsPreserveConstructible` | 6 | 1 | proof | 1 |
| `Sheaf.Paper.QcqsCompactSupportRealization` | 6 | 1 | proof | 1 |
| `Sheaf.Paper.StratifiedLattice` | 6 | 1 | proof | 1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic` | 6 | 6 | proof | 1 |
| `Sheaf.Paper.CompactSupportReductionTower` | 7 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | 7 | 1 | proof | 1 |
| `Sheaf.Paper.NormalizedDVREffectivity` | 7 | 1 | proof | 1 |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | 8 | 1 | proof | 1 |
| `Sheaf.Paper.ConstructibleTruncations` | 9 | 1 | proof | 1 |
| `Sheaf.Paper.FiniteCoefficientPoint` | 9 | 9 | proof | 1 |
| `Sheaf.Paper.PbcDescentFunctors` | 9 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | - | 1 | proof | 1 |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | - | 1 | proof | 1 |
| `Sheaf.Paper.AdicSmoothBaseChange` | - | 1 | proof | 1 |
| `Sheaf.Paper.AdmissibleVerdierExchange` | - | 1 | proof | 1 |
| `Sheaf.Paper.CanonicalOriginCompactSupportComposition` | - | 4 | proof | 1 |
| `Sheaf.Paper.CompactSupportProjectionFormula` | - | 9 | proof | 1 |
| `Sheaf.Paper.CompleteCompactSupportProetale` | - | 13 | proof | 1 |
| `Sheaf.Paper.CondensedERealization` | - | 1 | proof | 1 |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | - | 2 | proof | 1 |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | - | 9 | proof | 1 |
| `Sheaf.Paper.ConstantWeilStructure` | - | 3 | proof | 1 |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | - | 1 | proof | 1 |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | - | 1 | proof | 1 |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.ExchangeFunctoriality` | - | 10 | proof | 1 |
| `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange` | - | 13 | proof | 1 |
| `Sheaf.Paper.FiniteFieldInternalHomFiniteness` | - | 1 | proof | 1 |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | - | 1 | proof | 1 |
| `Sheaf.Paper.LisseCompletedSystemComparison` | - | 1 | proof | 1 |
| `Sheaf.Paper.LisseEConstructibleIntegralLattice` | - | 1 | proof | 1 |
| `Sheaf.Paper.LocalFrobeniusTrace` | - | 5 | proof | 1 |
| `Sheaf.Paper.PointFibreEquivalence` | - | 1 | proof | 1 |
| `Sheaf.Paper.PurAdicReconstruction` | - | 1 | proof | 1 |
| `Sheaf.Paper.PurityDivisorClass` | - | 2 | proof | 1 |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.QbarCompactSupportBaseChange` | - | 1 | proof | 1 |
| `Sheaf.Paper.QbarProperBaseChange` | - | 1 | proof | 1 |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | - | 16 | proof | 1 |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | - | 10 | proof | 1 |
| `Sheaf.Paper.TensorAdjunctionExchange` | - | 1 | proof | 1 |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | - | 1 | proof | 1 |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.CoefQbarVerdier` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.FiniteExceptional` | - | 9 | proof | 1 |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | - | 4 | proof | 1 |
| `Sheaf.SixFunctors.IntegralVerdier` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.RationalVerdier` | - | 1 | proof | 1 |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.KoszulReconstruction` | 4 | 1 | proof | 2 |
| `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality` | 4 | 3 | proof | 2 |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.DerivedNakayamaResolution` | 5 | 2 | proof | 2 |
| `Sheaf.Paper.FiniteProperBaseChange` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralCriterionReductions` | 5 | 8 | proof | 2 |
| `Sheaf.Paper.IntegralDerivedOperationsOnSlices` | 5 | 4 | proof | 2 |
| `Sheaf.Paper.IntegralModels` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralModelsOperations` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.SectionDerivedRealization` | 5 | 2 | proof | 2 |
| `Sheaf.Paper.WitnessCompatibility` | 5 | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | 5 | 1 | proof | 2 |
| `Sheaf.SixFunctors.ProEtale.DerivedCompletion` | 5 | 2 | proof | 2 |
| `Sheaf.SixFunctors.ScalarSixPullback` | 5 | 1 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionTensorComparison` | 6 | 7 | proof | 2 |
| `Sheaf.Paper.CartesianCoefficientTwists` | 6 | 5 | proof | 2 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.DerivedPullbackTensorIso` | 6 | 19 | proof | 2 |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | 6 | 13 | proof | 2 |
| `Sheaf.Paper.OpenImmersionTensorPiece` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | 6 | 3 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | 7 | 10 | proof | 2 |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.CompletedPullbackReduction` | 7 | 5 | proof | 2 |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | 7 | 27 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.WeilIndSheafCategory` | 7 | 8 | proof | 2 |
| `Sheaf.SecSmoothPurity.DirectImageScalarExchange` | 7 | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | 7 | 1 | proof | 2 |
| `Sheaf.SixFunctors.EtaleOpenTensor` | 7 | 2 | proof | 2 |
| `Sheaf.SixFunctors.FlatModelGeneration` | 7 | 3 | proof | 2 |
| `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.AdicStratifiedPerfect` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.CoefficientSystemDerivedComparison` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.ConstructiblePullbackTExact` | 8 | 4 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | 8 | 2 | proof | 2 |
| `Sheaf.Paper.PbcQbarCompletedPullback` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | 8 | 10 | proof | 2 |
| `Sheaf.Paper.PurTwistSheafLocallyFree` | 8 | 3 | proof | 2 |
| `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | 9 | 2 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | 9 | 8 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | 9 | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | 9 | 45 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | 9 | 14 | proof | 2 |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | 9 | 19 | proof | 2 |
| `Sheaf.Paper.StrictTowerExchangeMateNormalization` | 9 | 2 | proof | 2 |
| `Sheaf.Paper.CommonStageCalculus` | 10 | 8 | proof | 2 |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | 10 | 7 | proof | 2 |
| `Sheaf.Paper.PointSectionsFiniteness` | 10 | 1 | proof | 2 |
| `Sheaf.SixFunctors.OpenTensorNormalization` | 10 | 2 | proof | 2 |
| `Sheaf.Paper.DerivedNakayama` | 11 | 1 | proof | 2 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | 11 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.PurityRelativeCone` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting` | - | 4 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SupportedKummerScalarSource` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegration` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.LocalizationInverseImageCoherence` | - | 7 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 2 |
| `Sheaf.Paper.AdicPurityFiniteTensor` | - | 4 | proof | 2 |
| `Sheaf.Paper.AdicPurityRootComparisons` | - | 6 | proof | 2 |
| `Sheaf.Paper.AdicPuritySourceReduction` | - | 2 | proof | 2 |
| `Sheaf.Paper.AdicPurityTwistReduction` | - | 7 | proof | 2 |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | - | 11 | proof | 2 |
| `Sheaf.Paper.BoundaryDualizingComposition` | - | 1 | proof | 2 |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | - | 1 | proof | 2 |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 33 | proof | 2 |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | - | 9 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompletedExchangeCoherence` | - | 9 | proof | 2 |
| `Sheaf.Paper.CompletedScalarShift` | - | 1 | proof | 2 |
| `Sheaf.Paper.ConstructibleProjectionMates` | - | 1 | proof | 2 |
| `Sheaf.Paper.DeltaRestriction` | - | 4 | proof | 2 |
| `Sheaf.Paper.EtaleWeilFundamentalRepresentation` | - | 8 | proof | 2 |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | - | 2 | proof | 2 |
| `Sheaf.Paper.ExceptionalFiniteRealization` | - | 5 | proof | 2 |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | - | 6 | proof | 2 |
| `Sheaf.Paper.FieldWeilShriekShiftData` | - | 7 | proof | 2 |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | - | 4 | proof | 2 |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | - | 16 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | - | 8 | proof | 2 |
| `Sheaf.Paper.FiniteReductionChartCalculus` | - | 3 | proof | 2 |
| `Sheaf.Paper.FiniteReductionComparisons` | - | 8 | proof | 2 |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | - | 3 | proof | 2 |
| `Sheaf.Paper.FiniteTateSiteDescent` | - | 1 | proof | 2 |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | - | 7 | proof | 2 |
| `Sheaf.Paper.FrobeniusExchangeEquivalence` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralCompactSupportUniformRestriction` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralCtfTriangulated` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralDirectImageTower` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | - | 12 | proof | 2 |
| `Sheaf.Paper.IntegralHomReductionComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | - | 13 | proof | 2 |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | - | 5 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | - | 9 | proof | 2 |
| `Sheaf.Paper.PbcWeilCategory` | - | 7 | proof | 2 |
| `Sheaf.Paper.ProjectionCoefficientTensorTotal` | - | 4 | proof | 2 |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.ProperOpenTowerComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.PurityAffineLineOrientation` | - | 1 | proof | 2 |
| `Sheaf.Paper.PurityConventions` | - | 11 | proof | 2 |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | - | 2 | proof | 2 |
| `Sheaf.Paper.PurityFrameIndependence` | - | 1 | proof | 2 |
| `Sheaf.Paper.PurityGeneralAdmissibility` | - | 1 | proof | 2 |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | - | 1 | proof | 2 |
| `Sheaf.Paper.PuritySourceTransports` | - | 10 | proof | 2 |
| `Sheaf.Paper.RationalCompactSupportCoefficientCoherence` | - | 1 | proof | 2 |
| `Sheaf.Paper.RefinementExchangeCoherence` | - | 3 | proof | 2 |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | proof | 2 |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | - | 21 | proof | 2 |
| `Sheaf.Paper.SfLocalizationAllStages` | - | 2 | proof | 2 |
| `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian` | - | 1 | proof | 2 |
| `Sheaf.Paper.SmoothPurityMap` | - | 3 | proof | 2 |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | - | 1 | proof | 2 |
| `Sheaf.Paper.SupportedCupFunctoriality` | - | 13 | proof | 2 |
| `Sheaf.Paper.VectorBundlePurity` | - | 1 | proof | 2 |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | - | 1 | proof | 2 |
| `Sheaf.Paper.WeilTensorProduct` | - | 10 | proof | 2 |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | - | 4 | proof | 2 |
| `Sheaf.SixFunctors.BoundaryAlphaNormalization` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ClosedCostalkDuality` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | - | 5 | proof | 2 |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.CompositionProjectionMate` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | - | 3 | proof | 2 |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.FiniteDualizing` | - | 9 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | - | 3 | proof | 2 |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralDualizing` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralLisseReductionEquivalence` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | - | 2 | proof | 2 |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | - | 1 | proof | 2 |
| `Sheaf.TraceFormula.PointTransportComposition` | - | 2 | proof | 2 |
| `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence` | 6 | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientHeartFiltration` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.FinitePullbackTensorComparison` | 6 | 5 | proof | 3 |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 6 | 35 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | 3 |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | 6 | 1 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` | 7 | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CompactSupportRoosCofinality` | 7 | 2 | proof | 3 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | 7 | 4 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | 7 | 4 | proof | 3 |
| `Sheaf.Paper.IntegralCoherenceTower` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralTensorPullback` | 7 | 8 | proof | 3 |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | 7 | 7 | proof | 3 |
| `Sheaf.Paper.TateTwistLocallyFree` | 7 | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` | 7 | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport` | 8 | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | 8 | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows` | 8 | 3 | proof | 3 |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | 8 | 7 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | 8 | 7 | proof | 3 |
| `Sheaf.Paper.PurInverseImageTensorHom` | 8 | 1 | proof | 3 |
| `Sheaf.SmoothPurity.InternalAdjunctionEvaluation` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.AdicResidueLissePerfectLift` | 9 | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientHomZeroClass` | 9 | 1 | proof | 3 |
| `Sheaf.Paper.TorsionLimitSheafCompleteness` | 9 | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | 9 | 15 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint` | 10 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteLevelRectangle` | 10 | 1 | proof | 3 |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | 10 | 3 | proof | 3 |
| `Sheaf.Paper.RingedPushforwardCompletion` | 10 | 1 | proof | 3 |
| `Sheaf.SixFunctors.TensorProjectionAdjunct` | 10 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.BertiniIrreducibleMember` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor` | - | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ShriekTensorComposition` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | - | 3 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.SignedFibreTriangulated` | - | 1 | proof | 3 |
| `Sheaf.DeligneLaumon.BertiniSections` | - | 1 | proof | 3 |
| `Sheaf.Paper.AmbientCompleteRawSystem` | - | 7 | proof | 3 |
| `Sheaf.Paper.BoundedBelowCtfReflection` | - | 1 | proof | 3 |
| `Sheaf.Paper.CoefTowerCoaugmentation` | - | 1 | proof | 3 |
| `Sheaf.Paper.CohomologicalSmoothComposition` | - | 1 | proof | 3 |
| `Sheaf.Paper.CommonStageWeilShriek` | - | 5 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackUnitTower` | - | 3 | proof | 3 |
| `Sheaf.Paper.CompositeIntegrationCounit` | - | 6 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 9 | proof | 3 |
| `Sheaf.Paper.ConstantTowerDirectImageNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | - | 1 | proof | 3 |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | - | 5 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | - | 6 | proof | 3 |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | - | 3 | proof | 3 |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | - | 3 | proof | 3 |
| `Sheaf.Paper.FibreFunctorBasepointTransport` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteClosedShriek` | - | 8 | proof | 3 |
| `Sheaf.Paper.FiniteEtaleDescent` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteProjectionActionLaws` | - | 8 | proof | 3 |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | - | 1 | proof | 3 |
| `Sheaf.Paper.InternalSliceDerivedHomComparison` | - | 5 | proof | 3 |
| `Sheaf.Paper.LisseAdicAutomorphismPullback` | - | 13 | proof | 3 |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | - | 8 | proof | 3 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 10 | proof | 3 |
| `Sheaf.Paper.PointSectionsDerivedReduction` | - | 1 | proof | 3 |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurAdicScalarExtensionTorBound` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | - | 15 | proof | 3 |
| `Sheaf.Paper.PurityFiniteKummerLevel` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurityGysinStructure` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurityNormalCone` | - | 4 | proof | 3 |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurityRelativeKummer` | - | 1 | proof | 3 |
| `Sheaf.Paper.RationalStalkExact` | - | 1 | proof | 3 |
| `Sheaf.Paper.RelativeSupportBottomDescent` | - | 16 | proof | 3 |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedCoefficientProjectionCocycle` | - | 1 | proof | 3 |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | - | 13 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 7 | proof | 3 |
| `Sheaf.Paper.SmoothPurityReductionTowerNormalized` | - | 1 | proof | 3 |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | - | 4 | proof | 3 |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | - | 1 | proof | 3 |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | - | 1 | proof | 3 |
| `Sheaf.Paper.SupportedAffineLineHomotopy` | - | 6 | proof | 3 |
| `Sheaf.Paper.SupportedCup` | - | 4 | proof | 3 |
| `Sheaf.Paper.SupportedHomPullback` | - | 1 | proof | 3 |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | - | 5 | proof | 3 |
| `Sheaf.Paper.TrfDevissageGeneration` | - | 1 | proof | 3 |
| `Sheaf.Paper.WeilCompactSupportCohomology` | - | 3 | proof | 3 |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | - | 2 | proof | 3 |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | - | 3 | proof | 3 |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | - | 2 | proof | 3 |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | - | 2 | proof | 3 |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | - | 9 | proof | 3 |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | - | 3 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 20 | proof | 3 |
| `Sheaf.Paper.CompactSupportCoefficientChange` | 7 | 8 | proof | 4 |
| `Sheaf.Paper.CompactSupportFiniteAction` | 7 | 5 | proof | 4 |
| `Sheaf.Paper.CompletedProjectionCoherence` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.MateOpenRestriction` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.FiniteComparisonLocalizing` | 8 | 2 | proof | 4 |
| `Sheaf.Paper.IntegralConstructibleHeart` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.RingedProjectionTensorComposition` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.SystemNormalizedTensorClosure` | 8 | 2 | proof | 4 |
| `Sheaf.SecSmoothPurity.CochainTensorCoherenceData` | 9 | 4 | proof | 4 |
| `Sheaf.Paper.AdicConstructibleFiniteReductions` | 10 | 5 | proof | 4 |
| `Sheaf.Paper.InvertibleTensorScalarExtension` | 10 | 1 | proof | 4 |
| `Sheaf.Paper.WContractibleConstantReductionsML` | 10 | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedPresentationTransport` | 11 | 1 | proof | 4 |
| `Sheaf.Paper.RingedStrictTowerProjectionMorphism` | 11 | 1 | proof | 4 |
| `Sheaf.Paper.FiniteReductionConstructibility` | 12 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.KummerAffineLine` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.StandardGroupSchemes` | - | 12 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | - | 8 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | - | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | - | 7 | proof | 4 |
| `Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.FieldTheory.BertiniFieldExtension` | - | 1 | proof | 4 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.AffineLineOrdinaryInvariance` | - | 1 | proof | 4 |
| `Sheaf.Paper.AffineProjectiveComplexDerivedHom` | - | 1 | proof | 4 |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | - | 2 | proof | 4 |
| `Sheaf.Paper.CompactSupportSiteCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.DerivedReductionResolutionIndependence` | - | 5 | proof | 4 |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | - | 1 | proof | 4 |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteRingCompactSupportProjection` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteRingSectionDeformation` | - | 11 | proof | 4 |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | - | 1 | proof | 4 |
| `Sheaf.Paper.IntegralTwistScalarCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.KFlatConeComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | - | 2 | proof | 4 |
| `Sheaf.Paper.PointFibreDerivedTensor` | - | 1 | proof | 4 |
| `Sheaf.Paper.PointSectionsFiniteReduction` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProperCompactCoincidence` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProperOpenCoefficientMate` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurLisseMorphismRigidity` | - | 1 | proof | 4 |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | - | 2 | proof | 4 |
| `Sheaf.Paper.SiteComparisonEdgeSection` | - | 1 | proof | 4 |
| `Sheaf.Paper.SmoothPurityTowerBound` | - | 1 | proof | 4 |
| `Sheaf.Paper.SmoothPurityTowerInjectiveComponents` | - | 1 | proof | 4 |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | - | 1 | proof | 4 |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | - | 4 | proof | 4 |
| `Sheaf.Paper.TateInverseLimitBaseChange` | - | 12 | proof | 4 |
| `Sheaf.Paper.TwistFrobeniusScalar` | - | 10 | proof | 4 |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.ComparisonOpenTensorCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | - | 6 | proof | 4 |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | - | 1 | proof | 4 |
| `Sheaf.Paper.ConstantRealizationDerivedScalarExtension` | 5 | 4 | proof | 5 |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | 7 | 1 | proof | 5 |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | 7 | 7 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative` | 8 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | 9 | 7 | proof | 5 |
| `Sheaf.Paper.IntegralConstantModelHeart` | 9 | 1 | proof | 5 |
| `Sheaf.Paper.IntegralHeartLocalModel` | 9 | 9 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 10 | 9 | proof | 5 |
| `Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback` | 11 | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.RationalTermHomComparison` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` | - | 13 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence` | - | 5 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct` | - | 7 | proof | 5 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` | - | 7 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | - | 6 | proof | 5 |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | - | 4 | proof | 5 |
| `Sheaf.Paper.ConnectedConstantH0` | - | 3 | proof | 5 |
| `Sheaf.Paper.EtaleIsoDescent` | - | 1 | proof | 5 |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | - | 1 | proof | 5 |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | - | 1 | proof | 5 |
| `Sheaf.Paper.GlobalVerdierDuality` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralTwistBaseChange` | - | 1 | proof | 5 |
| `Sheaf.Paper.IteratedWeilCocycle` | - | 1 | proof | 5 |
| `Sheaf.Paper.PointCompletedEvaluation` | - | 3 | proof | 5 |
| `Sheaf.Paper.PointDerivedHomEvaluation` | - | 1 | proof | 5 |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | - | 1 | proof | 5 |
| `Sheaf.Paper.ProjectionFiniteReduction` | - | 1 | proof | 5 |
| `Sheaf.Paper.ProperProductCounitTranspose` | - | 1 | proof | 5 |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | - | 1 | proof | 5 |
| `Sheaf.Paper.StratifiedLatticeRank` | - | 1 | proof | 5 |
| `Sheaf.Paper.SystemClopenTensorCompatibility` | - | 1 | proof | 5 |
| `Sheaf.Paper.SystemTensorMateArrows` | - | 10 | proof | 5 |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.IntegralExpressionOccurrences` | - | 6 | proof | 5 |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | - | 4 | proof | 5 |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.OpenFactorCoherence` | - | 1 | proof | 5 |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | - | 2 | proof | 5 |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | - | 1 | proof | 5 |
| `Sheaf.TraceFormula.CompactFrobeniusTransportComposition` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CommutativeExchangeChart` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons` | - | 21 | proof | 6 |
| `Sheaf.Paper.ConstantTowerTransition` | - | 1 | proof | 6 |
| `Sheaf.Paper.ExternalRHomConePairing` | - | 1 | proof | 6 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | - | 1 | proof | 6 |
| `Sheaf.Paper.FiniteProductCompactification` | - | 2 | proof | 6 |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | - | 4 | proof | 6 |
| `Sheaf.Paper.InternalHomDualTorAmplitude` | - | 1 | proof | 6 |
| `Sheaf.Paper.PointReductionUnits` | - | 5 | proof | 6 |
| `Sheaf.Paper.PullbackCoefficientIterateCoherence` | - | 2 | proof | 6 |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | - | 1 | proof | 6 |
| `Sheaf.SecSmoothPurity.DerivedExchangeCube` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.CompletedTensorShiftRight` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` | - | 1 | proof | 7 |
| `Sheaf.Paper.KFlatMapFactorization` | - | 1 | proof | 7 |
| `Sheaf.Paper.PfRefinementCompatibility` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.PunctualTensorBaseChange` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.TruncationHomotopyColimit` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction` | - | 1 | proof | 9 |

## Stage 3: waiting for statements of dependencies (17)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | - | 12 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.Paper.DlConstructibleFibresExact` | - | 1 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.DualizingObjectPurity` | - | 1 | `lem-pur-projection-purity-agreement` |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | - | 1 | `def-pur-affine-space-comparison` |
| `Sheaf.Paper.FiniteFreeCompactComposition` | - | 8 | `lem-pur-system-level-projection-formula-coherence` |
| `Sheaf.Paper.FiniteReductionOfPurity` | - | 8 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.FiniteTorStability` | - | 15 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | - | 1 | `lem-pur-vector-integration-site-comparison` |
| `Sheaf.Paper.PurityCompositionCoherence` | - | 12 | `lem-pur-diagonal-dnc-chart-normalization` |
| `Sheaf.Paper.RationalPurityPresentation` | - | 13 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | - | 4 | `det-sp-tower-gamma` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | - | 7 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.VerdierExchange` | - | 1 | `sk-thm-sf-tensor-hom` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 8 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | - | 8 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.SixFunctors.RationalOperations` | - | 1 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.SmoothPurity.NormalizedWitness` | - | 1 | `lem-pur-condensed-exceptional-reconstruction` |

## Stage 3: held for an open upstream PR (15)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-six-functors-c1,bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | bundle/sec-smooth-purity-d2,prove2/sk-prop-sf-kunneth-ordinary |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
