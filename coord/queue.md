# Work queue

373 items; claim with `tools/claim.py next <group> [--stage N]`.

## Rework: quarantined by the upstream sync (15 clusters, 1467 modules)

Priority over every queue (the human, 2026-10-20; tools/rework.py, coord/rework.tsv). One item per cluster: its root (a quarantined module importing no other quarantined one) and the quarantined modules importing it; fix the root, then the dependents as far as possible, deliver every module that compiles.

| item (root) | modules | other roots | cause of the root |
|---|---|---|---|
| `Sheaf.Paper.FdCoefficientComparison` | 1 |  | error: Sheaf/Paper/FdCoefficientComparison.lean:195:2: failed to synthesize instance of type class |
| `Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | 1 |  | error: Sheaf/UpstreamExtra/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Colimit/TwoColimit.lean:134:10: Unknown identifier `factors` |
| `Sheaf.SixFunctors.ClosedImmersionTensorProjection` | 1 |  | error: Sheaf/SixFunctors/ClosedImmersionTensorProjection.lean:47:4: Type mismatch: After simplification, term |
| `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.SingleComplexQcqsHomologyMono` | 1 |  | error: Sheaf/AlgebraicGeometry/SingleComplexQcqsHomologyMono.lean:59:15: Unknown identifier `SingleComplexBaseChange.StalkCondition` |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTensorUnit` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.IntegralDerivedTensorBoundedTorsion` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence` | 1 |  | error: Sheaf/Paper/FiniteDiscreteCoefficientSquareCoherence.lean:254:6: Unknown constant `AlgebraicGeometry.Etale.pullbackSquareComparison_def` |
| `Sheaf.Algebra.Homology.AffineTildeTensorSourceComparisonCorePre` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.Paper.CondensedQbarPullbackCube` | 1 |  | error: Sheaf/Paper/CondensedQbarPullbackCube.lean:121:40: Unknown identifier `finiteCoefficientDerivedToAlgCl` |
| `Sheaf.AlgebraicGeometry.CanonicalTensorHomUncurryNormalizedComparison` | 1 |  | error: Sheaf/AlgebraicGeometry/CanonicalTensorHomUncurryNormalizedComparison.lean:174:12: error(lean.invalidField): Invalid field `IsAcyclicTensorKFlat`: The en |
| `Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |
| `Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` | 1 |  | error: failed in the global build after a cluster restore (see the build log) |

Blocked by rework (not in the queue until the rework items they depend on are fixed): stage 1 0, stage 2 154, stage 3 154 items.

## Stage 1: nodes to split (22)

| node | distance to a target | Lean state on the done branch |
|---|---|---|
| `lem-sbc-ambient-operations-scalar-linearity` | 3 | none |
| `lem-sfb-filtered-ring-object-cocone-colimit` | 1001 | none |
| `lem-cbc-ringed-open-extension-products` | 2004 | none |
| `lem-asd-affine-roots-representability` | 2005 | none |
| `lem-sfb-qcqs-integral-finite-model-completeness` | 2006 | none |
| `lem-sfb-qcqs-proper-integral-rational-scalar-comparison` | 2006 | none |
| `lem-sfb-qcqs-rational-integral-localizing-generators` | 2006 | none |
| `lem-sfb-qcqs-proper-serre-heart-bound` | 2007 | none |
| `lem-sfb-continuous-algcl-proper-scalar-comparison` | 4009 | none |
| `lem-sfb-continuous-algcl-tame-boundary-comparison` | 4009 | none |
| `lem-sfb-normal-continuous-algcl-monodromy` | 4009 | none |
| `lem-sfb-tame-pair-proper-generators` | 4009 | none |
| `det-def-sfb-filtered-two-colimit-characterization` | - | none |
| `det-def-sfb-filtered-two-colimit-model` | - | none |
| `lem-sfb-bounded-bifunctor-devissage` | - | none |
| `lem-sfb-finite-free-scalar-coordinates` | - | none |
| `lem-sfb-internal-extension-finite-presentation` | - | none |
| `lem-sfb-sheaf-pushforward-generator-comparison` | - | none |
| `lem-sfb-cohomology-tor-interval` | - | none |
| `def-per-support-condition` | - | none |
| `lem-dl-a1-galois-prime-residue-lifting` | - | none |
| `lem-dl-a1-integral-normal-residue-etale-splitting` | - | none |

## Stage 2: nodes to state (47)

| node | distance to Mathlib | kind | blockers |
|---|---|---|---|
| `def-sfb-finite-derived-adjunction` | 1 | state | 0 |
| `lem-pur-completed-primitive-counit-comparison` | 2 | state | 4 |
| `lem-per-adic-common-stage-truncations` | 1 | state | 2 |
| `lem-weil-point-finite-free-sections-tensor` | 1 | state | 2 |
| `det-picard-rr-duality` | 1 | state | 0 |
| `lem-a1-finite-pullback-strict-tower-comparison` | 1 | state | 0 |
| `lem-a1-roos-intrinsic-unit-comparison` | 1 | state | 0 |
| `lem-cbc-ringed-open-scalar-limit-coherence` | 1 | state | 0 |
| `lem-coef-enriched-sequence-projection-formula` | 1 | state | 0 |
| `lem-pc-curve-local-scalar-principal-parts` | 1 | state | 0 |
| `lem-pc-tate-residue-field-extension` | 1 | state | 0 |
| `lem-pur-affine-coordinate-support-stalk-continuity` | 1 | state | 0 |
| `lem-pur-concentrated-support-etale-transfer` | 1 | state | 0 |
| `lem-pur-etale-kflat-support-comparison` | 1 | state | 0 |
| `lem-pur-etale-sum-right-adjoint-tensor` | 1 | state | 0 |
| `lem-pur-exact-pullback-signed-comparison` | 1 | state | 0 |
| `lem-pur-finite-product-derived-tensor-calculus` | 1 | state | 0 |
| `lem-pur-finite-type-coordinate-support-orientation` | 1 | state | 0 |
| `lem-pur-normalized-operation-system-models` | 1 | state | 0 |
| `lem-pur-origin-class-projective-comparison` | 1 | state | 0 |
| `lem-pur-perfect-quotient-exchange-normalization` | 1 | state | 0 |
| `lem-pur-quotient-diagram-projection-evaluation` | 1 | state | 0 |
| `lem-pur-quotient-expression-kflat-normalization` | 1 | state | 0 |
| `lem-pur-sequence-adjoint-resolution-shifts` | 1 | state | 0 |
| `lem-pur-sequence-site-open-extension` | 1 | state | 0 |
| `lem-pur-signed-line-derived-base-change` | 1 | state | 0 |
| `lem-pur-strict-coefficient-comparison-calculus` | 1 | state | 0 |
| `lem-pur-support-comparison-section-model` | 1 | state | 0 |
| `lem-sf-boundary-bounded-tensor-comparison` | 1 | state | 0 |
| `lem-sf-cbc-localized-strict-tensor-descent` | 1 | state | 0 |
| `lem-sf-clopen-lisse-complete-localization` | 1 | state | 0 |
| `lem-sf-completed-pullback-mate-factorization` | 1 | state | 0 |
| `lem-sf-derived-completed-tensor-bilinearity` | 1 | state | 0 |
| `lem-sf-open-quotient-koszul-completeness` | 1 | state | 0 |
| `lem-sf-point-ringed-evaluation-model` | 1 | state | 0 |
| `lem-sf-tensor-comparison-localization-descent` | 1 | state | 0 |
| `lem-sfb-ordinary-proetale-direct-image-plus-comparison` | 1 | state | 0 |
| `lem-sp-normalized-error-tower-vanishing` | 1 | state | 0 |
| `lem-sp-power-torsion-sheaf-limit-complete` | 1 | state | 0 |
| `lem-sp-semilinear-kflat-tower-model` | 1 | state | 0 |
| `lem-trf-section-coordinate-counit-normalization` | 1 | state | 0 |
| `lem-weil-pbc-completed-scalar-unit-adjunction` | 1 | state | 0 |
| `lem-weil-pbc-finite-free-strict-tower-transport` | 1 | state | 0 |
| `lem-weil-pbc-pulled-reduction-normalization-comparison` | 1 | state | 0 |
| `lem-weil-pbc-quotient-diagram-scalar-projection` | 1 | state | 0 |
| `lem-weil-pbc-raw-restricted-class-normalization` | 1 | state | 0 |
| `lem-weil-ramified-pullback-tower-identification` | 1 | state | 0 |

Not open yet: 357 nodes that below a finished node, not needed, 10 nodes that wait for stage 1 (statement downstream not grounded), 118 nodes that wait for a statement dependency (bottom-up).

## Stage 3: modules to prove (282)

On the sorry route of an open batch, or below a route sorry of one (the human, 2026-10-18: provable as soon as every dependency is stated, whatever the depth); route first, then nearest to a route sorry.

| module | distance to a target | sorry | kind | route / steps to the nearest route sorry |
|---|---|---|---|---|
| `Sheaf.Paper.RingedTopoiCanonicalTensorPullback` | 4 | 1 | repair | route |
| `WeilConjectures.SixFunctors.Etale.Derived.Exchange` | 5 | 1 | repair | route |
| `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory` | 3 | 1 | disputed | 2 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal` | 3 | 10 | proof | route |
| `Sheaf.Paper.ProjectionMateExact` | 3 | 1 | proof | 1 |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | 3 | 1 | proof | 1 |
| `Sheaf.AlgebraicGeometry.CartierKummerMap` | - | 1 | proof | 1 |
| `Sheaf.Paper.ECoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients` | - | 21 | proof | 1 |
| `Sheaf.Paper.QbarCoefficientSmoothBaseChange` | - | 2 | proof | 1 |
| `Sheaf.Paper.ScalarModelFiniteFlatResolution` | - | 2 | proof | 1 |
| `Sheaf.Paper.CompletedDirectImageLimits` | 3 | 2 | proof | 2 |
| `Sheaf.Paper.IntegralStratifiedPerfectCharacterization` | 3 | 1 | proof | 2 |
| `Sheaf.Paper.PerfectProjectionFormula` | 3 | 3 | proof | 2 |
| `Sheaf.Paper.ConstantCompletionEquivalence` | 6 | 14 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsWellDefined` | 6 | 2 | proof | 2 |
| `Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.FiniteFreeResolutionTensor` | - | 4 | proof | 2 |
| `Sheaf.Algebra.Homology.InternalHomLocalizationComparison` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated` | - | 1 | proof | 2 |
| `Sheaf.Algebra.Homology.KInjectiveHomScalarTelescope` | - | 1 | proof | 2 |
| `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus` | - | 5 | proof | 2 |
| `Sheaf.AlgebraicGeometry.VectorProjectiveCompletion` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.CommonStageKaroubiInverse` | - | 9 | proof | 2 |
| `Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension` | - | 1 | proof | 2 |
| `Sheaf.CategoryTheory.InternalSectionScalarAdjunction` | - | 1 | proof | 2 |
| `Sheaf.Paper.AdicSmoothBaseChange` | - | 1 | proof | 2 |
| `Sheaf.Paper.AdicStratifiedPerfect` | - | 1 | proof | 2 |
| `Sheaf.Paper.AmbTateRootProjectionReduction` | - | 1 | proof | 2 |
| `Sheaf.Paper.AmbientCompleteCoefficientCategories` | - | 11 | proof | 2 |
| `Sheaf.Paper.AugmentedDiagramProjectionMate` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompleteCompactSupportProetale` | - | 13 | proof | 2 |
| `Sheaf.Paper.CompletedCoefficientPushforwardComparison` | - | 1 | proof | 2 |
| `Sheaf.Paper.CompletedOpenExchangeTransport` | - | 1 | proof | 2 |
| `Sheaf.Paper.DerivedPullbackTensorHom` | - | 12 | proof | 2 |
| `Sheaf.Paper.EtaleWeilSheafEquivalence` | - | 1 | proof | 2 |
| `Sheaf.Paper.FiniteFreeCompletedScalarComparison` | - | 5 | proof | 2 |
| `Sheaf.Paper.FiniteStagePairCategory` | - | 8 | proof | 2 |
| `Sheaf.Paper.FiniteStageRationalExchangeCoherence` | - | 3 | proof | 2 |
| `Sheaf.Paper.FiniteTateSiteDescent` | - | 1 | proof | 2 |
| `Sheaf.Paper.IntegralOperationsScalarComparisons` | - | 13 | proof | 2 |
| `Sheaf.Paper.PbcDescentFunctors` | - | 1 | proof | 2 |
| `Sheaf.Paper.PullbackTensorCanonicalShiftUnit` | - | 1 | proof | 2 |
| `Sheaf.Paper.QlbarTailModuleColimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent` | - | 1 | proof | 2 |
| `Sheaf.Paper.SbcCompletedOperations` | - | 15 | proof | 2 |
| `Sheaf.Paper.SfCbcCompactSupportCompositionLimit` | - | 1 | proof | 2 |
| `Sheaf.Paper.SupportedCupFunctoriality` | - | 13 | proof | 2 |
| `Sheaf.CategoryTheory.RingedSiteDualityMaps` | 4 | 4 | proof | 3 |
| `Sheaf.Paper.IntegralCompletedLocalPerfectCriterion` | 4 | 1 | proof | 3 |
| `Sheaf.Paper.RingedProjectionRestriction` | 4 | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` | 5 | 1 | proof | 3 |
| `Sheaf.Paper.IntegralScalarExtensionWellDefined` | 6 | 2 | proof | 3 |
| `Sheaf.Paper.EtaleProEtaleScalarMate` | 13 | 3 | proof | 3 |
| `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.DerivedTensorShiftDescent` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FieldComplexCohomologySplitting` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedOpenFlatResolution` | - | 2 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedOpenTotalTensorKFlat` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.SitePerfectScalarHomComparison` | - | 1 | proof | 3 |
| `Sheaf.Algebra.Homology.TotalTensorHomotopyConeSigns` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.FiniteRootSiteComparison` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.NormalizedImmersionComparisonCoherence` | - | 1 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing` | - | 3 | proof | 3 |
| `Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleProEtale` | - | 4 | proof | 3 |
| `Sheaf.CategoryTheory.AdicBasisLimit` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceGlobalSections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.CoefficientSequenceSectionsLimit` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ExactLinearKoszulFibre` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.KoszulFibreLinearDescent` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.NormalizedRoosShiftComparison` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectedAdjunctionCoefficientSquares` | - | 18 | proof | 3 |
| `Sheaf.CategoryTheory.ReflectorAdjunctionUnitFormulas` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.ScalarLocalizationDerivedHom` | - | 2 | proof | 3 |
| `Sheaf.CategoryTheory.SectionRingLaxPushforwardCoherence` | - | 11 | proof | 3 |
| `Sheaf.CategoryTheory.SequencePushforwardLimitProjections` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent` | - | 1 | proof | 3 |
| `Sheaf.CategoryTheory.UnitPowerCompleteness` | - | 1 | proof | 3 |
| `Sheaf.Paper.AdicPerfectModelCompleteReduction` | - | 1 | proof | 3 |
| `Sheaf.Paper.AdicPullbackPresentationTransport` | - | 4 | proof | 3 |
| `Sheaf.Paper.AdicStratumCompletionUnit` | - | 2 | proof | 3 |
| `Sheaf.Paper.AmbientCompleteRawSystem` | - | 7 | proof | 3 |
| `Sheaf.Paper.BoundaryQDefiningCompositeComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.ClosedSupportedScalarComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.CoefficientComplexRationalization` | - | 6 | proof | 3 |
| `Sheaf.Paper.CompletedExchangeCoherence` | - | 9 | proof | 3 |
| `Sheaf.Paper.CompletedKoszulReductionRoosTriangle` | - | 1 | proof | 3 |
| `Sheaf.Paper.CompletedPerfectScalarPullback` | - | 10 | proof | 3 |
| `Sheaf.Paper.CompletedRingStrictFiniteExchange` | - | 3 | proof | 3 |
| `Sheaf.Paper.ConstantScalarStrictUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.ConstantScalarUnitQuasiIsomorphism` | - | 1 | proof | 3 |
| `Sheaf.Paper.ContinuousCoefficientSliceNormalization` | - | 2 | proof | 3 |
| `Sheaf.Paper.DirectImageHomEvaluationSquare` | - | 1 | proof | 3 |
| `Sheaf.Paper.ExceptionalCoefficientComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteCoefficientPoint` | - | 9 | proof | 3 |
| `Sheaf.Paper.FiniteCompactSupportUniformTor` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldClosedSupport` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFieldLisseInternalHom` | - | 1 | proof | 3 |
| `Sheaf.Paper.FiniteFreeConstructibleScalarTransport` | - | 2 | proof | 3 |
| `Sheaf.Paper.FiniteFreeQuotientCompletion` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralAmbientOperationModels` | - | 10 | proof | 3 |
| `Sheaf.Paper.IntegralCoefficientPresentationComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralModelOpenClosedPieces` | - | 1 | proof | 3 |
| `Sheaf.Paper.IntegralModelsExtensionClosed` | - | 1 | proof | 3 |
| `Sheaf.Paper.IsomorphismComparisonNatural` | - | 2 | proof | 3 |
| `Sheaf.Paper.KFlatScalarComparisonNormalization` | - | 4 | proof | 3 |
| `Sheaf.Paper.OrdinaryCompletedIntegralPullback` | - | 9 | proof | 3 |
| `Sheaf.Paper.PbcDistinguishedDiagramLifting` | - | 1 | proof | 3 |
| `Sheaf.Paper.PbcPairFunctorShiftCoherence` | - | 1 | proof | 3 |
| `Sheaf.Paper.PerfectStrataUniformReductions` | - | 1 | proof | 3 |
| `Sheaf.Paper.PointAutomorphismRestrictionNatural` | - | 1 | proof | 3 |
| `Sheaf.Paper.PrincipalKoszulStrictReplacement` | - | 6 | proof | 3 |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | - | 1 | proof | 3 |
| `Sheaf.Paper.ProEtaleFiniteScalarRestrictionConstructible` | - | 3 | proof | 3 |
| `Sheaf.Paper.ProEtaleScalarMateNormalization` | - | 3 | proof | 3 |
| `Sheaf.Paper.ProperEtaleOriginScalarIsomorphism` | - | 1 | proof | 3 |
| `Sheaf.Paper.PurityFiniteKummerLevel` | - | 1 | proof | 3 |
| `Sheaf.Paper.RealWeilSheaves` | - | 2 | proof | 3 |
| `Sheaf.Paper.RegularQuotientCompletionUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedOpenStrictReduction` | - | 13 | proof | 3 |
| `Sheaf.Paper.RingedPullbackHomEvaluationComparison` | - | 1 | proof | 3 |
| `Sheaf.Paper.RingedTensorAdjunctionMate` | - | 1 | proof | 3 |
| `Sheaf.Paper.RoosIntrinsicCompletenessEquivalence` | - | 1 | proof | 3 |
| `Sheaf.Paper.ScalarCompletionAssociator` | - | 1 | proof | 3 |
| `Sheaf.Paper.SequenceSiteCompletionProjection` | - | 1 | proof | 3 |
| `Sheaf.Paper.SfCbcDirectImageReductionUnit` | - | 1 | proof | 3 |
| `Sheaf.Paper.ShiftedTensorMorphismCalculus` | - | 4 | proof | 3 |
| `Sheaf.Paper.StrictQuotientExchangeUnitEquation` | - | 1 | proof | 3 |
| `Sheaf.Paper.SupportedHomPullback` | - | 1 | proof | 3 |
| `Sheaf.Paper.SupportedTriangleMateIdentification` | - | 1 | proof | 3 |
| `Sheaf.Paper.SystemPushforwardRestrictionTransition` | - | 1 | proof | 3 |
| `Sheaf.RepresentationTheory.CommonIrreducibilityDetectingCover` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.OpenScalarTensorNormalization` | - | 1 | proof | 3 |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | - | 7 | proof | 3 |
| `Sheaf.Algebra.Homology.RingedTensorComplexConstraints` | 5 | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` | 5 | 9 | proof | 4 |
| `Sheaf.Paper.LevelwiseAdicTruncations` | 6 | 6 | proof | 4 |
| `Sheaf.Paper.PbcActualScalarPullback` | 15 | 2 | proof | 4 |
| `Sheaf.Algebra.Homology.CochainTensorModelRigidity` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints` | - | 4 | proof | 4 |
| `Sheaf.Algebra.Homology.RingIsomorphismTensorTransport` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedHomCompositionModel` | - | 3 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSignedBidualLocalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedDualComponents` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.RingedSiteBoundedEvaluationAssembly` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.SubcategoryLeftResolution` | - | 1 | proof | 4 |
| `Sheaf.Algebra.Homology.TotalTensorSignedCoherence` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.BertiniFiniteCoverIrreducibleSystem` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.BertiniPrescribedPointSmoothSystem` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.CoefficientCoconeComparisonAgreement` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ConstructibleLocalTorEtaleOrigin` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.DerivedImmersionComparisonNormalization` | - | 5 | proof | 4 |
| `Sheaf.AlgebraicGeometry.EtaleDirectImageScalarExchange` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.FlatConstructibleTensor` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.LocallyClosedClosureComparisonSquare` | - | 5 | proof | 4 |
| `Sheaf.AlgebraicGeometry.PointSheafInsertionCalculus` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection` | - | 2 | proof | 4 |
| `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula` | - | 1 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportSiteComparison` | - | 8 | proof | 4 |
| `Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization` | - | 6 | proof | 4 |
| `Sheaf.AlgebraicGeometry.TorsionLineSystemBaseChange` | - | 7 | proof | 4 |
| `Sheaf.AlgebraicGeometry.VaryingRingOperations` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.Abelian.DerivedRepresentableTransport` | - | 4 | proof | 4 |
| `Sheaf.CategoryTheory.CofinalRoosRestriction` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.DerivedTowerCounitProjections` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.FlatScalarKoszulTowerComparison` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.InjectiveTowerRoosShifts` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact` | - | 1 | proof | 4 |
| `Sheaf.CategoryTheory.TowerLimitTransposeNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.AutomorphismCompletionUnitComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.CoefficientExtensionReductionModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedCoefficientPullbackLinearity` | - | 8 | proof | 4 |
| `Sheaf.Paper.CompletedFiniteExchangeCoordinates` | - | 17 | proof | 4 |
| `Sheaf.Paper.CompletedStrictOpenExchange` | - | 7 | proof | 4 |
| `Sheaf.Paper.CompletedTensorScalarLinearity` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedTensorUnitInsertion` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletionUnitStrictQuotientModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.DerivedFiniteQuotientCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleDirectImageScalarComposition` | - | 2 | proof | 4 |
| `Sheaf.Paper.EtaleOpenScalarExchange` | - | 1 | proof | 4 |
| `Sheaf.Paper.EtaleSumCoefficientComputation` | - | 1 | proof | 4 |
| `Sheaf.Paper.ExactSectionsReductionUnit` | - | 1 | proof | 4 |
| `Sheaf.Paper.FiniteFreeCoefficientTransport` | - | 3 | proof | 4 |
| `Sheaf.Paper.FinitePullbackTensorComparison` | - | 5 | proof | 4 |
| `Sheaf.Paper.FlatScalarDirectImageLimitCoherence` | - | 1 | proof | 4 |
| `Sheaf.Paper.IntrinsicFiniteDerivedPullback` | - | 5 | proof | 4 |
| `Sheaf.Paper.IsomorphismScalarTensorKFlatModel` | - | 1 | proof | 4 |
| `Sheaf.Paper.OpenScalarSiteCoherence` | - | 8 | proof | 4 |
| `Sheaf.Paper.OrderedExchangeCoefficientComparison` | - | 10 | proof | 4 |
| `Sheaf.Paper.OrdinaryPullbackStratifiedModels` | - | 10 | proof | 4 |
| `Sheaf.Paper.PbcAutomorphismTransport` | - | 13 | proof | 4 |
| `Sheaf.Paper.PbcFiniteRawScalarComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.ProjectiveCohomologySplitModel` | - | 3 | proof | 4 |
| `Sheaf.Paper.ProjectiveTopCellAttachment` | - | 1 | proof | 4 |
| `Sheaf.Paper.PulledReductionStrictTowerComparison` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurAdicLineSystemBaseChange` | - | 1 | proof | 4 |
| `Sheaf.Paper.PurityRankOneLocalCalculation` | - | 1 | proof | 4 |
| `Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSitePerfectProjectionFormula` | - | 1 | proof | 4 |
| `Sheaf.Paper.RingedSliceComparisonsShift` | - | 1 | proof | 4 |
| `Sheaf.Paper.SfConstructibleCanonicalCompleteness` | - | 3 | proof | 4 |
| `Sheaf.Paper.SfExactPullbackCounitNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.SiteDerivedTensorRestriction` | - | 1 | proof | 4 |
| `Sheaf.Paper.StratumCompletionUnitRestriction` | - | 11 | proof | 4 |
| `Sheaf.Paper.StrictQuotientDiagonalNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.StrictQuotientPullbackComputation` | - | 1 | proof | 4 |
| `Sheaf.Paper.SupportedHomCocycleNormalization` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.CompletedCoefficientFreeResolution` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.EtaleOpenScalarCoherence` | - | 1 | proof | 4 |
| `Sheaf.SixFunctors.LocallyClosedClosureAdjointRealization` | - | 1 | proof | 4 |
| `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization` | - | 1 | proof | 4 |
| `Sheaf.Paper.CompletedTowerDirectImage` | 5 | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.BalancedTensorChain` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.LineUnboundedDerivedTensor` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.SliceTensorIntegerShiftCompatibility` | - | 3 | proof | 5 |
| `Sheaf.AlgebraicGeometry.AmpleOfAffineGeneratingLoci` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.CoordinateChartFiniteDimensionWitness` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoCartierCycleClass` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.GeoP1Cohomology` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.OpenCoverCohomologyDetection` | - | 10 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization` | - | 1 | proof | 5 |
| `Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest` | - | 4 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.GoodTruncationNormalization` | - | 7 | proof | 5 |
| `Sheaf.CategoryTheory.DerivedCategory.PerfectScalarTensorCoherence` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FlatScalarTowerExchange` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.FlatScalarTowerLimitSquare` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.OpenLeftProjectionAction` | - | 1 | proof | 5 |
| `Sheaf.CategoryTheory.RoosTransitionHomotopy` | - | 1 | proof | 5 |
| `Sheaf.Paper.CompletedLineTensorCoherence` | - | 23 | proof | 5 |
| `Sheaf.Paper.GeometricStalkPerfect` | - | 4 | proof | 5 |
| `Sheaf.Paper.IntegralLineReductionRestriction` | - | 1 | proof | 5 |
| `Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy` | - | 1 | proof | 5 |
| `Sheaf.Paper.RHomColimitCohomologyLadder` | - | 4 | proof | 5 |
| `Sheaf.Paper.ScalarPullbackComposition` | - | 1 | proof | 5 |
| `Sheaf.Paper.ScalarPullbackStrictConeNaturality` | - | 1 | proof | 5 |
| `Sheaf.Paper.SheafSliceDerivedComparison` | - | 1 | proof | 5 |
| `Sheaf.Paper.StrictQuotientScalarBalancing` | - | 1 | proof | 5 |
| `Sheaf.Algebra.Homology.KoszulRoosProjectionComparison` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ClassicalSupportCounitIdentification` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.CompleteLinearSystemClosed` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleHorizontalDoubleCounit` | - | 5 | proof | 6 |
| `Sheaf.AlgebraicGeometry.EtaleSumRightAdjointCoherence` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.FiniteFlatConstructibleTotalTensor` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Decomposition` | - | 1 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.ProEtaleSupportGlobalBoundary` | - | 6 | proof | 6 |
| `Sheaf.AlgebraicGeometry.SupportQuotientProduct` | - | 1 | proof | 6 |
| `Sheaf.Paper.ClassicalLocalizationTriangleTransport` | - | 1 | proof | 6 |
| `Sheaf.Paper.CommonLinePositiveScalarPowers` | - | 2 | proof | 6 |
| `Sheaf.Paper.DerivedLocalClassEdgeComparison` | - | 1 | proof | 6 |
| `Sheaf.Paper.EllCoefficientFiber` | - | 3 | proof | 6 |
| `Sheaf.Paper.SignedLineScalarPullbackSquare` | - | 1 | proof | 6 |
| `Sheaf.Paper.SignedLineScalarTensorTower` | - | 7 | proof | 6 |
| `Sheaf.Algebra.Homology.RegularQuotientConeAugmentation` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.RestrictedKFlatTensorIdentification` | - | 6 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility` | - | 1 | proof | 7 |
| `Sheaf.AlgebraicGeometry.SupportQuotientPairPullback` | - | 1 | proof | 7 |
| `Sheaf.CategoryTheory.SemilinearTensorPresentationTransport` | - | 1 | proof | 7 |
| `Sheaf.Compactification.NagataDensityNormalizationSetup` | - | 1 | proof | 7 |
| `Sheaf.Paper.CompletedCoefficientTensorNormalization` | - | 1 | proof | 7 |
| `Sheaf.Paper.FlatSingleScalarConventions` | - | 1 | proof | 7 |
| `Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction` | - | 1 | proof | 8 |
| `Sheaf.Algebra.Homology.SplitPerfectDualTorWindow` | - | 1 | proof | 8 |
| `Sheaf.Paper.FiniteScalarPerfectRefinement` | - | 1 | proof | 8 |
| `Sheaf.Paper.ScalarPerfectDualRealization` | - | 10 | proof | 8 |
| `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` | - | 1 | proof | 14 |
| `Sheaf.AlgebraicGeometry.CoherentAffineBaseChangeEdge` | - | 1 | proof | 16 |
| `Sheaf.AlgebraicGeometry.DerivedPullbackTopCohomology` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.TopBaseChangePresheaf` | - | 1 | proof | 17 |
| `Sheaf.AlgebraicGeometry.DerivedAdjunctionTopEdge` | - | 1 | proof | 18 |
| `Sheaf.AlgebraicGeometry.UnboundedDirectImageSectionPresheaf` | - | 1 | proof | 18 |

## Stage 3: waiting for statements of dependencies (60)

Not items: a node in the dependencies (stmt_deps or proof_deps) has no Lean statement yet (the human, 2026-10-17 and 2026-10-18).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 2 | `lem-sfb-integral-ambient-tower-comparison` |
| `WeilConjectures.ZetaFunction.TraceFormula` | 2 | 1 | `lem-zl-constant-geometric-stalk-unit` |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | 4 | 2 | `lem-sfb-integral-localization-hom-colimit` |
| `Sheaf.Algebra.Homology.PerfectTensorRoosCompletion` | - | 15 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization` | - | 1 | `lem-weil-pbc-raw-restricted-class-normalization` |
| `Sheaf.AlgebraicGeometry.FiniteDualityLocallyClosedComparison` | - | 2 | `lem-sf-locally-closed-relative-transpose-normalization` |
| `Sheaf.AlgebraicGeometry.SupportComparisonBoundary` | - | 1 | `lem-pur-support-comparison-section-model` |
| `Sheaf.CategoryTheory.FiniteFreeCompletionTransport` | - | 4 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.Paper.AdicHeartIntrinsicFibres` | - | 1 | `lem-per-adic-common-stage-truncations` |
| `Sheaf.Paper.CartesianCoefficientTwists` | - | 5 | `lem-pur-signed-line-derived-base-change` |
| `Sheaf.Paper.ClopenRoosIntegralDescent` | - | 12 | `lem-pur-finite-product-derived-tensor-calculus` |
| `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus` | - | 11 | `lem-coef-enriched-sequence-projection-formula` |
| `Sheaf.Paper.CompactSupportReductionTower` | - | 1 | `lem-pur-sequence-site-open-extension` |
| `Sheaf.Paper.CompleteProetaleStrictTowerRealization` | - | 9 | `lem-cbc-ringed-open-scalar-limit-coherence` |
| `Sheaf.Paper.CompletedOpenStrictMateIdentification` | - | 2 | `lem-cbc-ringed-open-scalar-limit-coherence` |
| `Sheaf.Paper.CompletedOperationTowerSubstitution` | - | 1 | `lem-pur-normalized-operation-system-models` |
| `Sheaf.Paper.CompletedProjectionCoherence` | - | 1 | `lem-pur-perfect-quotient-exchange-normalization` |
| `Sheaf.Paper.CompletedPullbackReduction` | - | 5 | `lem-weil-pbc-pulled-reduction-normalization-comparison` |
| `Sheaf.Paper.CondensedERealization` | - | 1 | `det-sp-rational-localized-hom` |
| `Sheaf.Paper.ConstructibleInternalHomContinuity` | - | 1 | `lem-sfb-bounded-finite-model-generation` |
| `Sheaf.Paper.ContinuousRationalDerivedRealization` | - | 1 | `lem-per-rational-pullback-composition-coherence` |
| `Sheaf.Paper.DirectImageChangeRingTranspose` | - | 1 | `lem-sp-proetale-scalar-tensor-normalization` |
| `Sheaf.Paper.FiniteClopenConstructibilityBounds` | - | 1 | `lem-pur-finite-product-derived-tensor-calculus` |
| `Sheaf.Paper.FiniteClopenDerivedDecomposition` | - | 16 | `lem-pur-finite-product-derived-tensor-calculus` |
| `Sheaf.Paper.FiniteRingSectionDeformation` | - | 11 | `lem-trf-section-coordinate-counit-normalization` |
| `Sheaf.Paper.IntegralCoherenceTower` | - | 1 | `lem-pur-quotient-expression-kflat-normalization` |
| `Sheaf.Paper.IntegralConstantModelHeart` | - | 1 | `lem-sfb-stratified-constant-model-product-bound` |
| `Sheaf.Paper.IntegralModelsOperations` | - | 1 | `lem-sfb-scalar-model-immersion-extension` |
| `Sheaf.Paper.IntegralPointTransportTowerRealization` | - | 1 | `lem-trf-point-transport-strict-quotient` |
| `Sheaf.Paper.IntegralPullbackComparisonRealization` | - | 1 | `lem-trf-counit-realization-substitution` |
| `Sheaf.Paper.IntegralPullbackCompletedComparison` | - | 1 | `lem-a1-roos-intrinsic-unit-comparison` |
| `Sheaf.Paper.IntegralTensorPullback` | - | 8 | `lem-sfb-integral-bounded-stratum-base-change` |
| `Sheaf.Paper.IsomorphismComparisonScalarExtension` | - | 5 | `lem-weil-isomorphism-scalar-augmentation-cone` |
| `Sheaf.Paper.LisseEConstructibleIntegralLattice` | - | 1 | `lem-weil-pbc-lisse-lattice-reduced-open` |
| `Sheaf.Paper.LocalWeilModelTraceIndependence` | - | 1 | `lem-fd-local-frobenius-coefficient-extension` |
| `Sheaf.Paper.LocalizingClosureCtfEqualsBc` | - | 1 | `lem-sfb-stratified-tor-interval-devissage` |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | - | 3 | `lem-pd-section-derived-open-adjunction-normalization` |
| `Sheaf.Paper.PbcScalarExtension` | - | 16 | `lem-weil-pbc-finite-free-strict-tower-transport` |
| `Sheaf.Paper.PointFibreDerivedTensor` | - | 1 | `lem-sf-point-ringed-evaluation-model` |
| `Sheaf.Paper.PointSectionsScalarExtension` | - | 14 | `lem-weil-point-finite-free-sections-tensor` |
| `Sheaf.Paper.PullbackIdentitiesScalarExtension` | - | 3 | `lem-pod-isomorphism-scalar-comparison-agreement` |
| `Sheaf.Paper.PurReductionLimitShiftAdjunction` | - | 1 | `lem-pur-sequence-adjoint-resolution-shifts` |
| `Sheaf.Paper.PurityConventions` | - | 11 | `sk-def-sf-operations` |
| `Sheaf.Paper.PurityGeneralAdmissibility` | - | 1 | `lem-pur-affine-chart-exceptional-identification` |
| `Sheaf.Paper.ResidueLisseProjectiveModels` | - | 1 | `lem-sf-clopen-lisse-complete-localization` |
| `Sheaf.Paper.ScalarExtensionTowerCoherence` | - | 7 | `lem-pur-strict-coefficient-comparison-calculus` |
| `Sheaf.Paper.SfCbcExtensionZeroCompletion` | - | 21 | `lem-sf-cbc-localized-strict-tensor-descent` |
| `Sheaf.Paper.SfImmersionCompletedPullbackComparison` | - | 19 | `lem-sf-completed-pullback-mate-factorization` |
| `Sheaf.Paper.SfIntegralCompactSupportConstructible` | - | 2 | `lem-sf-compact-support-proper-image-tower` |
| `Sheaf.Paper.SmoothPurityTowerReconstruction` | - | 4 | `lem-sp-semilinear-kflat-tower-model` |
| `Sheaf.Paper.SpecifiedPullbackComparisonAlpha` | - | 1 | `lem-weil-ramified-pullback-tower-identification` |
| `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` | - | 15 | `lem-sp-signed-tate-coefficient-exponent-normalization` |
| `Sheaf.SixFunctors.AdmissibleDirectImage` | - | 1 | `lem-sfb-continuous-algcl-open-finiteness` |
| `Sheaf.SixFunctors.AdmissibleTensorConstructibility` | - | 1 | `lem-sfb-continuous-qbar-constructible-generators` |
| `Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction` | - | 1 | `lem-sfb-identity-open-underived-square-normalization` |
| `Sheaf.SixFunctors.FiniteOpenDirectImageCtf` | - | 1 | `lem-sfb-ordinary-proetale-direct-image-plus-comparison` |
| `Sheaf.SixFunctors.FrobeniusPointTransportNatural` | - | 4 | `lem-weil-point-automorphism-transport-scalar-extension` |
| `Sheaf.SixFunctors.IntegralModelsGenerators` | - | 1 | `lem-sfb-lattice-subquotient-filtration` |
| `Sheaf.SixFunctors.IntegralOpenReductionComparison` | - | 1 | `lem-sf-open-quotient-koszul-completeness` |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | - | 5 | `lem-sfb-condensed-bounded-hom-continuity` |

## Stage 3: held for an open upstream PR (16)

Not items: an open Orchestra branch or PR of the source library proves the module (~/upstream-pr/upstream-pending.tsv, the human, 2026-10-18: do not duplicate Orchestra's open PRs); the routine sync brings the proof, and the hold ends when no sorry is left.

| module | source |
|---|---|
| `WeilConjectures.AlgebraicGeometry.Bertini` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | bundle/sec-deligne-laumon-general-d1 |
| `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1 |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs` | bundle/sec-smooth-purity-d3 |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal` | bundle/sec-smooth-purity-d1 |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | bundle/sec-poincare-duality-c1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | bundle/sec-six-functors-c1,bundle/sec-six-functors-d1,bundle/sec-smooth-purity-d3 |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | bundle/sec-poincare-duality-c1 |
| `WeilConjectures.WeilSheaf.PoincareDuality` | bundle/sec-poincare-duality-c1,bundle/sec-poincare-duality-d1 |
| `WeilConjectures.WeilSheaf.VerdierDual` | bundle/sec-deligne-laumon-a1-d1,bundle/sec-six-functors-d1 |
