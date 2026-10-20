# Work queue

642 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (1)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-trf-source-hyperext-module-target` | 4008 | none |

## Stage 2: nodes to state (30)

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
| `lem-wf-constant-twist-coefficient-comparison` | 1 | state | 0 |
| `lem-zl-proper-unit-condensed-realization` | 1 | state | 0 |
| `thm-pur-vector-bundle-thom` | 1 | state | 0 |
| `lem-coef-finite-scalar-mate-realization` | 2 | state | 0 |
| `lem-zl-compact-support-realization-factor-normalization` | 2 | state | 0 |
| `nt-target-poincare-isiso` | 2 | state | 0 |

Not open yet: 301 nodes that below a finished node, not needed, 85 nodes that wait for a statement dependency (bottom-up), 1 nodes that wait for stage 1 (statement downstream not grounded).

## Stage 3: modules to prove (611)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.AlgebraicGeometry.RelativeProjExists` | 10 | 1 | repair | route |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange` | 8 | 1 | repair | route |
| `Sheaf.Paper.SfHomTriangulated` | 7 | 1 | repair | route |
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | 5 | 1 | repair | route |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 6 | 3 | repair | route |
| `Sheaf.Paper.CompleteResidueCohomologyBounds` | 8 | 1 | repair | route |
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction` | 8 | 1 | disputed | 6 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` | 3 | 3 | proof | route |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | 3 | 1 | proof | route |
| `Sheaf.Paper.DerivedInternalHomFilteredColimit` | 3 | 6 | proof | route |
| `Sheaf.Paper.FiniteSmoothQuotientCoherence` | 3 | 1 | proof | route |
| `Sheaf.Paper.FiniteSmoothTwoLevelReduction` | 3 | 1 | proof | route |
| `Sheaf.Paper.IntegralHomReduction` | 3 | 1 | proof | route |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | route |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | route |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | 3 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus` | 4 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.CartierReductionSiteComparison` | 4 | 3 | proof | route |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 6 | proof | route |
| `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit` | 4 | 1 | proof | route |
| `Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties` | 4 | 1 | proof | route |
| `Sheaf.Paper.ProjectionFormulaArrows` | 4 | 6 | proof | route |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | route |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | 4 | 1 | proof | route |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | 4 | 1 | proof | route |
| `Sheaf.Paper.CompleteCompactSupportProetale` | 5 | 13 | proof | route |
| `Sheaf.Paper.CompletedKoszulQuotientComparison` | 5 | 1 | proof | route |
| `Sheaf.Paper.LisseNormalizedTowerLocalModels` | 5 | 1 | proof | route |
| `Sheaf.Paper.NormalizedDVREffectivity` | 5 | 1 | proof | route |
| `Sheaf.Paper.NormalizedTowerCommonLisseStrata` | 5 | 1 | proof | route |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | 5 | 2 | proof | route |
| `Sheaf.Paper.ringedProjectionFormula_totalization_left` | 5 | 1 | proof | route |
| `Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullbackBase` | 6 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleDirectImageRestrictionOfScalars` | 6 | 2 | proof | route |
| `Sheaf.CategoryTheory.DerivedCategory.DualizingComplexBoundedDuality` | 6 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedSitePerfectDuality` | 6 | 1 | proof | route |
| `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy` | 6 | 1 | proof | route |
| `Sheaf.Paper.CartesianCoefficientTwists` | 6 | 5 | proof | route |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | 6 | 11 | proof | route |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | 6 | 1 | proof | route |
| `Sheaf.Paper.DeltaRestriction` | 6 | 4 | proof | route |
| `Sheaf.Paper.DualityPairing` | 6 | 2 | proof | route |
| `Sheaf.Paper.IntegralCompactSupportUniformRestriction` | 6 | 1 | proof | route |
| `Sheaf.Paper.LisseEConstructibleIntegralLattice` | 6 | 1 | proof | route |
| `Sheaf.Paper.PurTwistSheafLocallyFree` | 6 | 3 | proof | route |
| `Sheaf.Paper.PuritySectionInvariantIntrinsic` | 6 | 1 | proof | route |
| `Sheaf.Paper.RingedModelCurryingCoherence` | 6 | 1 | proof | route |
| `Sheaf.SixFunctors.EtaleHomThickLocus` | 6 | 2 | proof | route |
| `Sheaf.SixFunctors.FiniteDualitySiteComparison` | 6 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal` | 7 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose` | 7 | 1 | proof | route |
| `Sheaf.Algebra.Homology.SignedDoubleHomCone` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ConormalGradedAlgebra` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EllAdicProperConstructibleCohomology` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.FixSiteOpenExchangeSheaf` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.ShriekTensorComposition` | 7 | 1 | proof | route |
| `Sheaf.Paper.CoefTowerCoaugmentation` | 7 | 1 | proof | route |
| `Sheaf.Paper.CoefficientEvaluationDerivedLeftAdjoint` | 7 | 3 | proof | route |
| `Sheaf.Paper.CompletedConstructibleReductionControl` | 7 | 1 | proof | route |
| `Sheaf.Paper.CompletedExtensionZeroComparison` | 7 | 19 | proof | route |
| `Sheaf.Paper.EtaleDerivedScalarTensor` | 7 | 1 | proof | route |
| `Sheaf.Paper.FiniteClopenExceptionalRestriction` | 7 | 1 | proof | route |
| `Sheaf.Paper.FiniteCompactSupportScalarTransport` | 7 | 1 | proof | route |
| `Sheaf.Paper.FiniteCompactificationStalkReturn` | 7 | 1 | proof | route |
| `Sheaf.Paper.FiniteFreeHomComparison` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralInverseImageComparisonComposition` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralLineTensorCompleteness` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackSystemComparison` | 7 | 1 | proof | route |
| `Sheaf.Paper.IntegralScalarExtensionConstructible` | 7 | 5 | proof | route |
| `Sheaf.Paper.IntegralTensorProduct` | 7 | 1 | proof | route |
| `Sheaf.Paper.ProperOpenRefinementAdjointProjection` | 7 | 1 | proof | route |
| `Sheaf.Paper.PurityRelativeKummer` | 7 | 1 | proof | route |
| `Sheaf.Paper.RefinementBoundaryVanishing` | 7 | 1 | proof | route |
| `Sheaf.Paper.SemilinearOperationsExistence` | 7 | 1 | proof | route |
| `Sheaf.Paper.SemilinearSystemsExistence` | 7 | 1 | proof | route |
| `Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility` | 7 | 1 | proof | route |
| `Sheaf.Paper.SignedTwistReductionComparison` | 7 | 1 | proof | route |
| `Sheaf.SixFunctors.CoefTowerEvaluationPairing` | 7 | 1 | proof | route |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData` | 7 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AffineTraceLineLocalization` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.CurveOpenDimensionGeneral` | 8 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization` | 8 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedPresentationTransport` | 8 | 1 | proof | route |
| `Sheaf.CategoryTheory.SystemLevelLeftExtension` | 8 | 2 | proof | route |
| `Sheaf.Paper.CompletionMateComparison` | 8 | 21 | proof | route |
| `Sheaf.Paper.ContinuousAlgClProperLowerTail` | 8 | 1 | proof | route |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | 8 | 1 | proof | route |
| `Sheaf.Paper.PurityFiniteKummerLevel` | 8 | 1 | proof | route |
| `Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates` | 8 | 1 | proof | route |
| `Sheaf.Algebra.Homology.RingHomExtensionDifferential` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.AffineTraceLineOpenCounitBaseChange` | 9 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization` | 9 | 1 | proof | route |
| `Sheaf.Paper.AdicReductionCohomologySequence` | 9 | 1 | proof | route |
| `Sheaf.Paper.AdicSuppliedModelFlatCriterion` | 9 | 1 | proof | route |
| `Sheaf.Paper.AdicTorFlatCriterion` | 9 | 1 | proof | route |
| `Sheaf.Paper.CommonStageCompactSupportExactness` | 9 | 1 | proof | route |
| `Sheaf.Paper.ContinuousAlgClProperHeartFiniteness` | 9 | 1 | proof | route |
| `Sheaf.Paper.IntegralPullbackReductionCounit` | 9 | 1 | proof | route |
| `Sheaf.Paper.KoszulQuotientConeIsIso` | 9 | 1 | proof | route |
| `Sheaf.Paper.PointDerivedHomEvaluation` | 9 | 1 | proof | route |
| `Sheaf.Paper.PurityAffineLineSupportStalk` | 9 | 1 | proof | route |
| `Sheaf.Paper.ScalarPullbackComposition` | 9 | 1 | proof | route |
| `Sheaf.Paper.SiteBoundedTruncationModels` | 9 | 1 | proof | route |
| `Sheaf.Paper.TorsionLimitSheafCompleteness` | 9 | 1 | proof | route |
| `Sheaf.SecSmoothPurity.ReductionDirectImage` | 9 | 2 | proof | route |
| `Sheaf.SixFunctors.AdmissibleDirectImage` | 9 | 1 | proof | route |
| `Sheaf.SixFunctors.AdmissibleTensorConstructibility` | 9 | 1 | proof | route |
| `Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition` | 10 | 1 | proof | route |
| `Sheaf.Algebra.Homology.PerfectRingHomTensorPrecomposition` | 10 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedCoefficientRestrictionCoefficientChange` | 10 | 1 | proof | route |
| `Sheaf.CategoryTheory.RingedCoefficientRestrictionDerivedPresentation` | 10 | 1 | proof | route |
| `Sheaf.Paper.UniformConstructibleExtIntegral` | 10 | 1 | proof | route |
| `Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeIsIso` | 11 | 1 | proof | route |
| `Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeMap` | 11 | 1 | proof | route |
| `Sheaf.Paper.IntegralProperReductionModel` | 11 | 1 | proof | route |
| `Sheaf.Paper.ProperHeartBoundLattice` | 11 | 1 | proof | route |
| `Sheaf.SixFunctors.SchemeGeometricFrobenius` | 11 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleNearRegularCoordinateFibre` | 12 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.OpenSourceComposition` | 12 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SmoothClosedCoordinateLift` | 12 | 1 | proof | route |
| `Sheaf.Paper.EtaleIntegralLineDerivedComplete` | 12 | 1 | proof | route |
| `Sheaf.Paper.EtaleIntegralLineReductions` | 12 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.SupportedProductLocalization` | 14 | 6 | proof | route |
| `Sheaf.AlgebraicGeometry.EtaleConstantProjectionFormula` | 15 | 1 | proof | route |
| `Sheaf.Paper.ExternalRHomConePairing` | 15 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.CoherentEtaleComparisonMorphismExists` | 19 | 1 | proof | route |
| `Sheaf.AlgebraicGeometry.QcoherentNormalizedComparison` | 20 | 1 | proof | route |
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
| `Sheaf.Paper.ProperBaseChangeRational` | 4 | 6 | proof | 1 |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.AdicSmoothBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.BasicOperationsCoefficientReduction` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.CanonicalOriginCompactSupportComposition` | 5 | 4 | proof | 1 |
| `Sheaf.Paper.CartesianCoefficients` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.CartesianCoefficientsFiniteFree` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportReductionTower` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.CondensedERealization` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.ConstantCoefficientScalarNormalization` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` | 5 | 9 | proof | 1 |
| `Sheaf.Paper.ConstantWeilStructure` | 5 | 3 | proof | 1 |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.EtaleCompactSupportCoefficientChange` | 5 | 3 | proof | 1 |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | 5 | 6 | proof | 1 |
| `Sheaf.Paper.FiniteCoefficientHomChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.FiniteCoefficientPoint` | 5 | 9 | proof | 1 |
| `Sheaf.Paper.FiniteConstructibleHom` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.FiniteExtensionCompactSupportBaseChange` | 5 | 13 | proof | 1 |
| `Sheaf.Paper.FiniteLevelProEtaleBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.FiniteStageVerdierBiduality` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralConstructibleInternalHom` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralOperationsPreserveConstructible` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.LisseCompletedSystemComparison` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.LocalFrobeniusTrace` | 5 | 5 | proof | 1 |
| `Sheaf.Paper.PbcDescentFunctors` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.PointFibreEquivalence` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.PurAdicReconstruction` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | 5 | 2 | proof | 1 |
| `Sheaf.Paper.QbarCompactSupportBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.QbarProperBaseChange` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.QcqsCompactSupportRealization` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.RationalCoefficientCategoryComparison` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.RationalSmoothPurityCanonical` | 5 | 16 | proof | 1 |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | 5 | 10 | proof | 1 |
| `Sheaf.Paper.StratifiedLattice` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.ZlFiniteAdicDirectImage` | 5 | 1 | proof | 1 |
| `Sheaf.Paper.ZlImmersionWeilLocalBehavior` | 5 | 1 | proof | 1 |
| `Sheaf.SixFunctors.BoundaryDualityDischarge` | 5 | 1 | proof | 1 |
| `Sheaf.SixFunctors.CoefQbarVerdier` | 5 | 1 | proof | 1 |
| `Sheaf.SixFunctors.IntegralVerdier` | 5 | 1 | proof | 1 |
| `Sheaf.SixFunctors.RationalVerdier` | 5 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | 6 | 1 | proof | 1 |
| `Sheaf.Paper.ConstructibleTruncations` | 6 | 1 | proof | 1 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | 6 | 12 | proof | 1 |
| `Sheaf.Paper.ExceptionalAdjointAdmissibility` | 6 | 1 | proof | 1 |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | 6 | 21 | proof | 1 |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | 6 | 4 | proof | 1 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Adjunction` | 7 | 1 | proof | 1 |
| `Sheaf.Paper.IntegralCohomologicalAdicCriterion` | 7 | 1 | proof | 1 |
| `Sheaf.Paper.PurityDivisorClass` | 10 | 2 | proof | 1 |
| `Sheaf.Paper.AdmissibleVerdierExchange` | - | 1 | proof | 1 |
| `Sheaf.Paper.CompactSupportProjectionFormula` | - | 9 | proof | 1 |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | - | 1 | proof | 1 |
| `Sheaf.Paper.ExchangeFunctoriality` | - | 10 | proof | 1 |
| `Sheaf.Paper.FiniteFieldInternalHomFiniteness` | - | 1 | proof | 1 |
| `Sheaf.Paper.TensorAdjunctionExchange` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.CoefVerdierWeilEquivariance` | - | 1 | proof | 1 |
| `Sheaf.SixFunctors.FiniteExceptional` | - | 9 | proof | 1 |
| `Sheaf.Paper.AdicCoefficientDatum` | 4 | 5 | proof | 2 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 4 | 24 | proof | 2 |
| `Sheaf.Paper.KoszulReconstruction` | 4 | 1 | proof | 2 |
| `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality` | 4 | 3 | proof | 2 |
| `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.CompactificationCoherenceCocycle` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.DerivedNakayamaFirstReduction` | 5 | 1 | proof | 2 |
| `Sheaf.Paper.DerivedNakayamaResolution` | 5 | 2 | proof | 2 |
| `Sheaf.Paper.EtaleWeilFundamentalRepresentation` | 5 | 8 | proof | 2 |
| `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` | 5 | 1 | proof | 2 |
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
| `Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` | 6 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting` | 6 | 4 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | 6 | 10 | proof | 2 |
| `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons` | 6 | 11 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorBundleIntegration` | 6 | 1 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionTensorComparison` | 6 | 7 | proof | 2 |
| `Sheaf.CategoryTheory.LocalizationInverseImageCoherence` | 6 | 7 | proof | 2 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.AdicPuritySourceReduction` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | 6 | 11 | proof | 2 |
| `Sheaf.Paper.BoundaryDualizingComposition` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.BoundaryProEtaleProjectionComparison` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.BoundaryProEtaleQCompatibility` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CoefficientSystemDerivedComparison` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CohomologicalSmoothnessTheorem` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CommonStageCalculus` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.CompactSupportFiniteFieldIndependence` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.CompletedExchangeCoherence` | 6 | 9 | proof | 2 |
| `Sheaf.Paper.CompletedPullbackReduction` | 6 | 5 | proof | 2 |
| `Sheaf.Paper.CompletedScalarShift` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.ConstructiblePullbackTExact` | 6 | 4 | proof | 2 |
| `Sheaf.Paper.DerivedPullbackTensorIso` | 6 | 19 | proof | 2 |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | 6 | 16 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientReductionFlatModel` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteHomArrow` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteExtensionReductionConeBound` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCoefficientExtension` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | 6 | 5 | proof | 2 |
| `Sheaf.Paper.FiniteReductionAffineOrientation` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.FiniteReductionComparisons` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.FiniteSmoothPullbackExchange` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.IntegralCompactSupportPrescribedReductions` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralConstructibleBoundedBelowCompactness` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralCtfTriangulated` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralExceptionalInverseImage` | 6 | 12 | proof | 2 |
| `Sheaf.Paper.IntegralHomReductionComparison` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | 6 | 13 | proof | 2 |
| `Sheaf.Paper.IntegralPointTransportTowerPowers` | 6 | 13 | proof | 2 |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.InternalAdjunctionPairingChange` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.OpenImmersionTensorPiece` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PbcQbarCompletedPullback` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PbcScalarExtension` | 6 | 45 | proof | 2 |
| `Sheaf.Paper.PointSectionsFiniteness` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PointSectionsScalarExtension` | 6 | 14 | proof | 2 |
| `Sheaf.Paper.ProEtaleSectionModuleFunctors` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.PurityAffineLineOrientation` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PurityDiagonalDualizingObject` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.PurityGeneralAdmissibility` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.PuritySourceTransports` | 6 | 10 | proof | 2 |
| `Sheaf.Paper.RationalCompactSupportCoefficientCoherence` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.RefinementExchangeCoherence` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.SbcCompletedOperations` | 6 | 15 | proof | 2 |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | 6 | 19 | proof | 2 |
| `Sheaf.Paper.SfLocalizationAllStages` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.SmoothPurityMap` | 6 | 3 | proof | 2 |
| `Sheaf.Paper.StratumAmbientHom` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.StrictTowerExchangeMateNormalization` | 6 | 2 | proof | 2 |
| `Sheaf.Paper.VectorBundlePurity` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.WeilIndSheafCategory` | 6 | 8 | proof | 2 |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | 6 | 1 | proof | 2 |
| `Sheaf.Paper.WeilTensorProduct` | 6 | 10 | proof | 2 |
| `Sheaf.SecSmoothPurity.DirectImageScalarExchange` | 6 | 1 | proof | 2 |
| `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.BoundaryAlphaNormalization` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.ClosedCostalkDuality` | 6 | 2 | proof | 2 |
| `Sheaf.SixFunctors.CoefIntegralFiniteExtension` | 6 | 5 | proof | 2 |
| `Sheaf.SixFunctors.ConstructibleTensorCompletion` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.EtaleOpenTensor` | 6 | 2 | proof | 2 |
| `Sheaf.SixFunctors.FiniteCoefficientVerdier` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.FlatModelGeneration` | 6 | 3 | proof | 2 |
| `Sheaf.SixFunctors.FrobeniusPointTransport` | 6 | 3 | proof | 2 |
| `Sheaf.SixFunctors.IntegralDualizing` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralLisseReductionEquivalence` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | 6 | 1 | proof | 2 |
| `Sheaf.SixFunctors.OpenTensorNormalization` | 6 | 2 | proof | 2 |
| `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` | 6 | 1 | proof | 2 |
| `Sheaf.TraceFormula.PointTransportComposition` | 6 | 2 | proof | 2 |
| `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport` | 7 | 2 | proof | 2 |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.CompletedPullbackTensorComparison` | 7 | 27 | proof | 2 |
| `Sheaf.Paper.ExceptionalDerivedSiteRealization` | 7 | 2 | proof | 2 |
| `Sheaf.Paper.FieldWeilShriekShiftData` | 7 | 7 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientAdjointComparisons` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteTateSiteDescent` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.FrobeniusCoefficientTwistsCanonical` | 7 | 7 | proof | 2 |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | 7 | 5 | proof | 2 |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | 7 | 9 | proof | 2 |
| `Sheaf.Paper.PbcWeilCategory` | 7 | 7 | proof | 2 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | 7 | 10 | proof | 2 |
| `Sheaf.SecSmoothPurity.ProperFiniteCoefficientExtension` | 7 | 1 | proof | 2 |
| `Sheaf.SixFunctors.FiniteDualizing` | 7 | 9 | proof | 2 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | 7 | 1 | proof | 2 |
| `Sheaf.Paper.AdicPurityTwistReduction` | 8 | 7 | proof | 2 |
| `Sheaf.Paper.AdicStratifiedPerfect` | 8 | 1 | proof | 2 |
| `Sheaf.Paper.FiniteCoefficientSiteScalarArrow` | 8 | 2 | proof | 2 |
| `Sheaf.Paper.FiniteReductionChartCalculus` | 8 | 3 | proof | 2 |
| `Sheaf.Paper.PurityConventions` | 8 | 11 | proof | 2 |
| `Sheaf.SixFunctors.CompactCoefficientComposition` | 8 | 2 | proof | 2 |
| `Sheaf.Paper.AdicPurityFiniteTensor` | 9 | 4 | proof | 2 |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | 9 | 9 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | 9 | 1 | proof | 2 |
| `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | 9 | 7 | proof | 2 |
| `Sheaf.Paper.ExceptionalFiniteRealization` | 9 | 5 | proof | 2 |
| `Sheaf.Paper.ExceptionalProEtaleRealization` | 9 | 6 | proof | 2 |
| `Sheaf.Paper.AdicPurityRootComparisons` | 10 | 6 | proof | 2 |
| `Sheaf.Paper.DerivedNakayama` | 10 | 1 | proof | 2 |
| `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian` | 10 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns` | 11 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.PurityRelativeCone` | 11 | 1 | proof | 2 |
| `Sheaf.Paper.IntegralDirectImageTower` | 11 | 1 | proof | 2 |
| `Sheaf.Paper.PurityFrameIndependence` | 11 | 1 | proof | 2 |
| `Sheaf.Paper.SmoothPurityNormalizedEquivalence` | 11 | 1 | proof | 2 |
| `Sheaf.Paper.SupportedCupFunctoriality` | 11 | 13 | proof | 2 |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | 11 | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SupportedKummerScalarSource` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompactSupportCondensedRealization` | - | 33 | proof | 2 |
| `Sheaf.Paper.ConstructibleProjectionMates` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteAdjointMateCompatibility` | - | 4 | proof | 2 |
| `Sheaf.Paper.FiniteDncNormalizationReduction` | - | 1 | proof | 2 |
| `Sheaf.Paper.FrobeniusExchangeEquivalence` | - | 1 | proof | 2 |
| `Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.ProjectionCoefficientTensorTotal` | - | 4 | proof | 2 |
| `Sheaf.Paper.ProjectionTensorCoefficientComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.ProperOpenTowerComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | - | 21 | proof | 2 |
| `Sheaf.Paper.WfTensorCompletionFrobenius` | - | 4 | proof | 2 |
| `Sheaf.SixFunctors.CompositionProjectionMate` | - | 1 | proof | 2 |
| `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization` | - | 3 | proof | 2 |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | - | 2 | proof | 2 |
| `Sheaf.Paper.CompletedAdicCoefficientDatum` | 5 | 9 | proof | 3 |
| `Sheaf.Paper.UnboundedProperOpenInterchange` | 5 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.BertiniIrreducibleMember` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.IntegralModelsStacks` | 6 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence` | 6 | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage` | 6 | 1 | proof | 3 |
| `Sheaf.DeligneLaumon.BertiniSections` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientHeartFiltration` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.CompletedCoefficientPresentationTransport` | 6 | 7 | proof | 3 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | 6 | 4 | proof | 3 |
| `Sheaf.Paper.ExplicitExceptionalPreservation` | 6 | 3 | proof | 3 |
| `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteProperLocalizing` | 6 | 3 | proof | 3 |
| `Sheaf.Paper.FinitePullbackTensorComparison` | 6 | 5 | proof | 3 |
| `Sheaf.Paper.IntegralCompactSupportCoefficientComparison` | 6 | 35 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | 3 |
| `Sheaf.Paper.LisseAdicAutomorphismPullback` | 6 | 13 | proof | 3 |
| `Sheaf.Paper.ProEtaleProperOpenInterchange` | 6 | 1 | proof | 3 |
| `Sheaf.Paper.WeilCompactSupportCohomology` | 6 | 3 | proof | 3 |
| `Sheaf.SixFunctors.BrownHypothesesSmall` | 6 | 1 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.AffineSpaceAmbientAdjunction` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport` | 7 | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | 7 | 2 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOrigin` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows` | 7 | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.VectorBundleZeroSection` | 7 | 3 | proof | 3 |
| `Sheaf.CategoryTheory.CompactSupportRoosCofinality` | 7 | 2 | proof | 3 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | 7 | 4 | proof | 3 |
| `Sheaf.Paper.AmbientCompleteRawSystem` | 7 | 7 | proof | 3 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | 7 | 4 | proof | 3 |
| `Sheaf.Paper.CohomologicalSmoothComposition` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.DegreeZeroDerivedMapGluing` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.EtaleCoefficientSystemAdjoint` | 7 | 5 | proof | 3 |
| `Sheaf.Paper.EtaleCompactScalarCoherence` | 7 | 6 | proof | 3 |
| `Sheaf.Paper.FiniteClosedShriek` | 7 | 8 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientSiteChainTensor` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteEtaleDescent` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.FiniteLevelRectangle` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralCoherenceTower` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralTensorPullback` | 7 | 8 | proof | 3 |
| `Sheaf.Paper.LocalFrobeniusTransportNormalization` | 7 | 8 | proof | 3 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | 7 | 10 | proof | 3 |
| `Sheaf.Paper.PointSectionsDerivedReduction` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.ProjectionFormulaCoefficientCoherence` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.PurEtaleScalarMateProjection` | 7 | 2 | proof | 3 |
| `Sheaf.Paper.PurityDiagonalSectionPasting` | 7 | 15 | proof | 3 |
| `Sheaf.Paper.PurityGysinStructure` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.PurityNormalCone` | 7 | 4 | proof | 3 |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.RationalStalkExact` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.RingedPushforwardCompletion` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | 7 | 7 | proof | 3 |
| `Sheaf.Paper.SupportedHomPullback` | 7 | 1 | proof | 3 |
| `Sheaf.Paper.TateTwistLocallyFree` | 7 | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` | 7 | 2 | proof | 3 |
| `Sheaf.SixFunctors.CoefTowerNaturalCurrying` | 7 | 1 | proof | 3 |
| `Sheaf.SixFunctors.CoefTowerTraceRectification` | 7 | 9 | proof | 3 |
| `Sheaf.SixFunctors.FiniteMappingAdjunction` | 7 | 1 | proof | 3 |
| `Sheaf.SmoothPurity.InternalAdjunctionEvaluation` | 7 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FrobeniusTrivializationPullback` | 8 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint` | 8 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.SiteClosedCounitTransport` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientHomZeroClass` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.CommonStageWeilShriek` | 8 | 5 | proof | 3 |
| `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` | 8 | 3 | proof | 3 |
| `Sheaf.Paper.IntegralComparisonSequenceSystems` | 8 | 7 | proof | 3 |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.PurInverseImageTensorHom` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | 8 | 1 | proof | 3 |
| `Sheaf.Paper.SupportedCup` | 8 | 4 | proof | 3 |
| `Sheaf.SecSmoothPurity.ClosedUnitAllStages` | 8 | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.ReductionExceptional` | 8 | 2 | proof | 3 |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | 8 | 15 | proof | 3 |
| `Sheaf.SixFunctors.TensorProjectionAdjunct` | 8 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite` | 9 | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars` | 9 | 2 | proof | 3 |
| `Sheaf.Paper.AdicResidueLissePerfectLift` | 9 | 1 | proof | 3 |
| `Sheaf.Paper.BoundedBelowCtfReflection` | 9 | 1 | proof | 3 |
| `Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus` | 9 | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.PurEtaleClosedConstantTensor` | 12 | 2 | proof | 3 |
| `Sheaf.CategoryTheory.SignedFibreTriangulated` | 12 | 1 | proof | 3 |
| `Sheaf.Paper.RelativeSupportBottomDescent` | 12 | 16 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | 12 | 7 | proof | 3 |
| `Sheaf.Paper.SmoothPurityReductionTowerNormalized` | 12 | 1 | proof | 3 |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | 12 | 4 | proof | 3 |
| `Sheaf.Paper.SmoothPurityTowerShriekLevels` | 12 | 1 | proof | 3 |
| `Sheaf.Paper.SupportedAffineLineHomotopy` | 12 | 6 | proof | 3 |
| `Sheaf.Paper.TowerCompactSupportProjectionFormula` | 12 | 5 | proof | 3 |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | 12 | 3 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | 12 | 20 | proof | 3 |
| `Sheaf.Paper.ConstantTowerDirectImageNormalization` | 15 | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.ArithmeticLiftFibrePath` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarLocalizationUnderlyingTelescope` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPullbackUnitTower` | - | 3 | proof | 3 |
| `Sheaf.Paper.CompositeIntegrationCounit` | - | 6 | proof | 3 |
| `Sheaf.Paper.CondensedCompactSupportProjection` | - | 9 | proof | 3 |
| `Sheaf.Paper.FibreFunctorBasepointTransport` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteProjectionActionLaws` | - | 8 | proof | 3 |
| `Sheaf.Paper.InternalSliceDerivedHomComparison` | - | 5 | proof | 3 |
| `Sheaf.Paper.PurAdicScalarExtensionTorBound` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedCoefficientProjectionCocycle` | - | 1 | proof | 3 |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | - | 13 | proof | 3 |
| `Sheaf.Paper.TrfDevissageGeneration` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.AdicScalarTraceCoherence` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.FiniteGeneralRing` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.MixedBaseChange` | - | 1 | proof | 3 |
| `Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` | - | 2 | proof | 3 |
| `Sheaf.SecSmoothPurity.ReductionCompatibilities` | - | 3 | proof | 3 |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.FiniteAdjunctionTransition` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompactSupportCoefficientChange` | 6 | 8 | proof | 4 |
| `Sheaf.Paper.CompactSupportFiniteAction` | 6 | 5 | proof | 4 |
| `Sheaf.Paper.FiniteRingSectionDeformation` | 6 | 11 | proof | 4 |
| `Sheaf.FieldTheory.BertiniFieldExtension` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.CompletedProjectionCoherence` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.FiniteReductionConstructibility` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.MateOpenRestriction` | 7 | 1 | proof | 4 |
| `Sheaf.Paper.NoetherianEtaleSectionSpecialization` | 7 | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleExceptionalConstantTensor` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.KummerAffineLine` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison` | 8 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | 8 | 8 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution` | 8 | 2 | proof | 4 |
| `Sheaf.Paper.CompactSupportSiteCoherence` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.DerivedReductionResolutionIndependence` | 8 | 5 | proof | 4 |
| `Sheaf.Paper.FiniteComparisonLocalizing` | 8 | 2 | proof | 4 |
| `Sheaf.Paper.FinitePointInternalHomEvaluation` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.IntegralConstructibleHeart` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.PointSectionsFiniteReduction` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.ProperOpenCoefficientMate` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.RingedProjectionTensorComposition` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.RingedStrictTowerProjectionMorphism` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.SiteComparisonEdgeSection` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.SystemNormalizedTensorClosure` | 8 | 2 | proof | 4 |
| `Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization` | 8 | 1 | proof | 4 |
| `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso` | 8 | 6 | proof | 4 |
| `Sheaf.SixFunctors.FrobeniusFixedPoints` | 8 | 1 | proof | 4 |
| `Sheaf.SixFunctors.SchemeGaloisCoefficientChange` | 8 | 1 | proof | 4 |
| `Sheaf.Paper.AcyclicFlatProperCoefficientModel` | 9 | 1 | proof | 4 |
| `Sheaf.Paper.InvertibleTensorScalarExtension` | 9 | 1 | proof | 4 |
| `Sheaf.Paper.KFlatConeComparison` | 9 | 1 | proof | 4 |
| `Sheaf.Paper.PointFibreDerivedTensor` | 9 | 1 | proof | 4 |
| `Sheaf.Paper.TateInverseLimitBaseChange` | 9 | 12 | proof | 4 |
| `Sheaf.SecSmoothPurity.CochainTensorCoherenceData` | 9 | 4 | proof | 4 |
| `Sheaf.Paper.AdicConstructibleFiniteReductions` | 10 | 5 | proof | 4 |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | 10 | 1 | proof | 4 |
| `Sheaf.Paper.ProperCompactCoincidence` | 10 | 1 | proof | 4 |
| `Sheaf.Paper.WContractibleConstantReductionsML` | 10 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.KunnethSupported` | 13 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | 13 | 7 | proof | 4 |
| `Sheaf.CategoryTheory.FirstQuadrantLowestRowEdge` | 13 | 1 | proof | 4 |
| `Sheaf.Paper.AffineLineOrdinaryInvariance` | 13 | 1 | proof | 4 |
| `Sheaf.Paper.SfProEtaleProjectionFormula` | 13 | 2 | proof | 4 |
| `Sheaf.Paper.SmoothPurityTowerInjectiveComponents` | 13 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FundamentalGroup.FiniteEtaleFieldLimitDescent` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackCoherence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.StandardGroupSchemes` | - | 12 | proof | 4 |
| `Sheaf.CategoryTheory.RingedToposBinaryDescent` | - | 1 | proof | 4 |
| `Sheaf.Paper.AffineProjectiveComplexDerivedHom` | - | 1 | proof | 4 |
| `Sheaf.Paper.CohomologicalSmoothEtaleLocality` | - | 2 | proof | 4 |
| `Sheaf.Paper.FiniteFreeCompactSupportComposition` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteRingCompactSupportProjection` | - | 1 | proof | 4 |
| `Sheaf.Paper.FrobeniusOperatorCompactDescription` | - | 1 | proof | 4 |
| `Sheaf.Paper.IntegralTwistScalarCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurLisseMorphismRigidity` | - | 1 | proof | 4 |
| `Sheaf.Paper.SmoothPurityTowerBound` | - | 1 | proof | 4 |
| `Sheaf.Paper.SmoothPurityTowerP1Adjunction` | - | 1 | proof | 4 |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | - | 4 | proof | 4 |
| `Sheaf.Paper.TwistFrobeniusScalar` | - | 10 | proof | 4 |
| `Sheaf.SixFunctors.ComparisonOpenTensorCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.NormalizedTowerTensorEvaluation` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | 4 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | 5 | 1 | proof | 5 |
| `Sheaf.Paper.ConstantRealizationDerivedScalarExtension` | 5 | 4 | proof | 5 |
| `Sheaf.Paper.CompactSupportRepresentativeIndependence` | 7 | 1 | proof | 5 |
| `Sheaf.Paper.IntegralCompactSupportCoefficientData` | 7 | 7 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative` | 8 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 8 | 9 | proof | 5 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | 8 | 7 | proof | 5 |
| `Sheaf.Paper.BrownExceptionalAdjoint` | 8 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate` | 9 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.NormalizedSupportTriangle` | 9 | 13 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct` | 9 | 7 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | 9 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.SupportedExteriorProduct` | 9 | 7 | proof | 5 |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | 9 | 4 | proof | 5 |
| `Sheaf.Paper.ConnectedConstantH0` | 9 | 3 | proof | 5 |
| `Sheaf.Paper.IntegralConstantModelHeart` | 9 | 1 | proof | 5 |
| `Sheaf.Paper.IntegralHeartLocalModel` | 9 | 9 | proof | 5 |
| `Sheaf.Paper.StratifiedLatticeRank` | 9 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.AdicFiniteStratificationPullback` | 11 | 1 | proof | 5 |
| `Sheaf.Paper.PointFibreDerivedTensorBasic` | 11 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OrdinaryKunnethFiniteRing` | 14 | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.RelativeHigherDirectImageContinuity` | 14 | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.RationalTermHomComparison` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtalePullbackStalkCoherence` | - | 5 | proof | 5 |
| `Sheaf.Paper.EtaleIsoDescent` | - | 1 | proof | 5 |
| `Sheaf.Paper.FiniteForwardProductSymmetry` | - | 1 | proof | 5 |
| `Sheaf.Paper.FrobeniusPullbackComparisonCoherence` | - | 1 | proof | 5 |
| `Sheaf.Paper.GlobalVerdierDuality` | - | 1 | proof | 5 |
| `Sheaf.Paper.IntegralTwistBaseChange` | - | 1 | proof | 5 |
| `Sheaf.Paper.IteratedWeilCocycle` | - | 1 | proof | 5 |
| `Sheaf.Paper.PointCompletedEvaluation` | - | 3 | proof | 5 |
| `Sheaf.Paper.ProjectionFiniteReduction` | - | 1 | proof | 5 |
| `Sheaf.Paper.ProperProductCounitTranspose` | - | 1 | proof | 5 |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | - | 1 | proof | 5 |
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
| `Sheaf.Paper.ConstantTowerTransition` | 10 | 1 | proof | 6 |
| `Sheaf.Paper.PointReductionUnits` | 10 | 5 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportedLocalizationComparisons` | 15 | 21 | proof | 6 |
| `Sheaf.Paper.FiniteFieldDerivedTensorSummand` | 15 | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.CommutativeExchangeChart` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals` | - | 1 | proof | 6 |
| `Sheaf.Paper.FiniteProductCompactification` | - | 2 | proof | 6 |
| `Sheaf.Paper.InternalHomDualConstructibleModels` | - | 4 | proof | 6 |
| `Sheaf.Paper.InternalHomDualTorAmplitude` | - | 1 | proof | 6 |
| `Sheaf.Paper.PullbackCoefficientIterateCoherence` | - | 2 | proof | 6 |
| `Sheaf.Paper.PurIntegralTwistLineInverseImage` | - | 1 | proof | 6 |
| `Sheaf.SecSmoothPurity.DerivedExchangeCube` | - | 1 | proof | 6 |
| `Sheaf.SixFunctors.CompletedTensorShiftRight` | - | 1 | proof | 6 |
| `Sheaf.Paper.KFlatMapFactorization` | 16 | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.FiniteAffineProetaleRefinement` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent` | - | 1 | proof | 7 |
| `Sheaf.Paper.PfRefinementCompatibility` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.TruncationHomotopyColimit` | 8 | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.PunctualTensorBaseChange` | - | 1 | proof | 8 |
| `Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison` | - | 1 | proof | 9 |
| `Sheaf.AlgebraicGeometry.PrimeTorsionCoefficientReduction` | - | 1 | proof | 9 |

## Stage 3: waiting for statements of dependencies (17)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.SmoothPurity.NormalizedWitness` | 1 | 1 | `lem-pur-condensed-exceptional-reconstruction` |
| `Sheaf.Paper.FiniteCoefficientSmoothPurity` | 5 | 1 | `def-pur-affine-space-comparison` |
| `Sheaf.Paper.FiniteReductionOfPurity` | 5 | 8 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.FiniteTorStability` | 5 | 15 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.SixFunctors.RationalOperations` | 5 | 1 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.Paper.AdicSmoothDualizingComplexes` | 6 | 12 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.Paper.DualizingObjectPurity` | 6 | 1 | `lem-pur-projection-purity-agreement` |
| `Sheaf.Paper.PurityCompositionCoherence` | 6 | 12 | `lem-pur-diagonal-dnc-chart-normalization` |
| `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose` | 6 | 8 | `lem-coef-finite-scalar-mate-realization` |
| `Sheaf.Paper.DlConstructibleFibresExact` | 8 | 1 | `lem-tw-lisse-rational-realization` |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | 10 | 4 | `det-sp-tower-gamma` |
| `Sheaf.Paper.RelativeSupportCoordinateModel` | 13 | 7 | `cor-pur-affine-space-zero-section-purity` |
| `Sheaf.Paper.FiniteFreeCompactComposition` | - | 8 | `lem-pur-system-level-projection-formula-coherence` |
| `Sheaf.Paper.FiniteUniversalSmoothTrace` | - | 1 | `lem-pur-vector-integration-site-comparison` |
| `Sheaf.Paper.RationalPurityPresentation` | - | 13 | `lem-pur-adic-purity-scalar-naturality` |
| `Sheaf.Paper.VerdierExchange` | - | 1 | `sk-thm-sf-tensor-hom` |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | - | 8 | `lem-pur-adic-purity-scalar-naturality` |

## Stage 3: held for an open upstream PR (11)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.Compactification.Refinement` | bundle/sec-deligne-laumon-a1-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary` | bundle/sec-smooth-purity-d2,prove2/sk-prop-sf-kunneth-ordinary |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
