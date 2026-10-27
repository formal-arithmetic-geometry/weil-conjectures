# Semilinear proper/open scalar proofs and elaboration scopes

## Reason

Prove the two scalar comparison invertibility holes using the ordinary and derived
scalar comparison packages. Carrier transports and chosen adjunctions otherwise
cause costly definitional equality. Private normalization lemmas compare the
specified functors and mates through section formulas and localization APIs.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The private comparison previously asserted only nonemptiness:

```lean
private theorem scalar_rho_iso
    (D : VaryingRing.OrdinaryScalarComparison C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
    (X : Scheme.{u}) : Nonempty (D.rho X ≅ rhoOrdinary C τ B φ hφ X)
```

The existing two public theorems `rhoPullInv_isIso` and `rhoR_isIso` contain `sorry`.
The ordinary scalar functor is defined by the unique functor specification, and
its direct-image comparison is characterized by identity on sections.

## New

The two theorems have complete proofs. The new scalar-derived dependency is a
private proof import with access to the existing proved `scalarD_isIso` helper.
The proof uses this direct-image component rather than the full derived comparison
conjunction and its unrelated alpha proof. The ordinary scalar functor retains its identical signature and choice body. Public definitions,
statement signatures and public imports retain their meaning.

The private comparison now records its section normalization, needed by both
scalar-mate proofs. Its consumers are all in this module:

```lean
private theorem restriction_rho_iso
    (D : VaryingRing.OrdinaryScalarRestriction C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
    (X : Scheme.{u}) : ∃ e : D.rho X ≅ rhoOrdinary C τ B φ hφ X,
      ∀ (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
        (x : (((D.rho X).obj M).obj (op n)).val.obj H),
        HEq (((e.hom.app M).app (op n)).val.app H x) x
```

The normalization proof is factored through a new private `restriction_rho_iso`
for the smaller ordinary scalar restriction record. The unused old `scalar_rho_iso` is removed; a repository scan finds no external
consumer. Exactness uses only the restriction
record. The chosen ordinary direct-image comparison, inverse mate and open-extension
isomorphism use its adjunction record. A general mate-normalization proof over these
records is specialized to the full record only for the derived comparison.

The file retains the original exported category instance; declaration-local
scopes disable it only while elaborating selected private normalization proofs.
The temporary broad erasure and restoration are removed. New irreducibility,
implicit-reducibility and composition-instance attributes are local to proof
sections.
Evaluation now reuses the canonical `VaryingRing.moduleEvalP`. Its specified
forward section formula and inverse-hom identity give both normalization formulas.
The existing private normalization statement is retained as a wrapper for import-all
consumers, while a separate canonical helper records the chosen comparison.
Abstract section extensionality is shared. The ordinary evaluation inverse mate is
identified once with the constant diagram of `moduleEvalG`; all three evaluation
proofs reuse this proved normalization. The forward and inverse localization
composition equations for a constant-diagram square are proved over abstract exact
functors and instantiated in the concrete derived and open evaluation arguments. The general restriction construction obtains
a sequence natural transformation together with its component equations, keeping
the transformation abstract in its naturality calculation. The open comparison specializes the
existing proved exact-localization inverse-mate theorem. The private `exact_hom_fac`,
`normalized_square` and inverse-mate signatures used by consumers are preserved.
The direct `DerivedMateComparison` import is removed.

The ordinary restriction construction now uses a proved private lemma over an
arbitrary site and ring family. Specializing it preserves the existing unique
functor specification and its chosen functor, while keeping concrete coefficient
sheaves out of the generic section calculations.

The file uses sequential proof elaboration (`Elab.async false`) and disables
generated injectivity lemmas. The private section-carrier comparison, structural-map comparison and pushforward
construction use local instance-search budgets of 64. The file uses a search budget of 32 to avoid
unnecessary branching, and the coherence statements treat `alpha` and `gamma`
through their declared types with local irreducibility attributes. The coefficient-transition
wrapper and the derived functor wrappers have local `implicit_reducible` attributes
so that the same coefficient model is recognized under implicit transparency. The
large sheafification and localization constructions remain locally irreducible.
This includes `HasDerivedCategory.standard`, `DerivedCategory.Q` and
`Functor.mapDerivedCategoryFactors`. Ordinary `SemilinearSections.evaluation` is
locally irreducible after its section normalizations.
The model ring and structural coefficient maps are locally irreducible after
their construction; module pushforward is locally irreducible after its section
normalization proof. The constant-diagram comparison is locally irreducible in
the evaluation section after ordinary normalization; proved component formulas
expose its hom and inverse. Its definition and the generic mate identity are
unchanged. The pushforward coherence proof batches its section rewrites, preserving
the original transparency settings while avoiding repeated goal checks.

```lean
-- In each of the ScalarRestriction and Evaluation sections:
attribute [local implicit_reducible]
  VaryingRing.coefficientTransition StrictTower.G StrictTower.R P R
-- Additionally in the scalar proof section:
attribute [local implicit_reducible] VaryingRing.ordinaryScalarMap
-- In the general restriction construction:
attribute [local implicit_reducible] SemilinearSections.ringPresheaf
```
Transparency is enabled for the new categorical and ordinary scalar arguments;
existing proofs that need the original transparency mode retain scoped settings.
No new instance or attribute is exported. Debug profiling options and markers
are removed. No target statement or interpretation changes.

## Users

Only the assigned module (held by U1) is edited. The source-only downstream scan
finds 529 transitive consumers. All keep the same public declarations,
definitions and imports, so none needs source adaptation. A declaration-use scan
finds `rhoOrdinary` only in the assigned module. The six import-all consumers
were also checked for private-helper uses; all helper interfaces they use remain
identical, so none requires an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | U1 | Two proofs and private proof helpers. |
| `Sheaf.AlgebraicGeometry.ProperOpenRefinementMatePlusCompatibility` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.DeligneLaumon.Reduction.FiniteMapPurity` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.FourierTransform.FourierDeligneTransform` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicCompletedProjectionShift` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicExceptionalNormalizationMate` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicExceptionalShiftCoherence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicMiddleExtensionConstructible` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicNormalizedPurityLift` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftCoherence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicProjectionShiftData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicProperAdjunctionRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityCanonicalSourceCoherence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityNormalizedComparisonConstruction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicPurityScalarNaturalityData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicQbarConstructibleRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicTraceTensorShift` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeCoefficientCalculus` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicTraceTransposeData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceConstruction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceCounitReductions` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceProjectionAssembly` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceReductionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceScalarData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTargetNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTensorCoordinates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdicUnitTraceTransposeReductions` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AdmissibleVerdierExchange` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceLastFactorProduct` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceProductDomain` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceContractionProduct` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceFactorization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceProductData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.AffineSpaceTraceSuccessorContraction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ChernFlagFormula` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CoefficientGammaRepresentatives` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CoefficientTowerGeometricComposition` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageCurveWeilMiddleExtension` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageFourierTransform` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageSmoothOperationIdentification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageWeilFourierTransform` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CommonStageWeilShriek` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportCondensedRealization` | Y2 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportLimitEquationData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportLimitEquationRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportPathReductionSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportProjectionFormula` | C3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationFactorization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportRealizationIdentity` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactSupportTowerReduction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactificationBOrdinaryProjectionSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionDomains` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompactificationBProjectionReduction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompleteIntegralConstantRestriction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompleteProjectionDescentMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompleteProjectionMateDescent` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompleteProjectionReductionSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompositionComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompositionModelOrientationDefinitions` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompositionModelOrientationDescent` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CompositionTensorMate` | G8 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalCounitRepresentation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRealizationProperties` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstruction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalReconstructionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalRefinementCounits` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedExceptionalSystemRecognition` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedOpenCoefficientModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitRealizationSupport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedOpenCounitUnits` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CondensedOpenUnitComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ConstantPurityFrobeniusSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CoordinateCartierBoundarySign` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CoordinateSectionProjectiveTrace` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CoordinateSectionSiteTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CoordinateSectionTensorTrace` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CoprojectionCompositionMate` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.DiagramOpenClopenShiftModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.DlConstantFieldCharts` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.DlConstructibleFibresExact` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.EtaleOrientationLocality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.EtaleSystemScalarMateCoherence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.EvenLineBinaryProductNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.EvenLineCoefficientProjectionNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.EvenLineCoordinateIntertwining` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.EvenLineProductIntegrationMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.EvenLineProductIntegrationSymmetry` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.EvenTateLineSelfSymmetry` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ExactProperOpenProjectionMate` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ExceptionalBaseChangeIntegralMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ExceptionalRealizationNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionContext` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ExceptionalReconstructionPresentations` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemAdjoints` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemComparison` | M9 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemComponents` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemDomains` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemEvaluation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemFiniteComposite` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemIso` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldExceptionalSystemLaws` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldProjectionOriginWitnesses` | W8 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldPuritySystemTranspose` | C1 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldPurityTransposeArrows` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldPurityTransposeLevelWords` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FieldWeilShriekShiftData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FilteredCondensedCanonicalComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FilteredCondensedCounitBijective` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FilteredCondensedCounitFiniteFormula` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FilteredCondensedRepresentingPair` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FilteredCondensedRepresentingPairData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationEigenvalues` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationStalkReturn` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteCompactificationWeilExact` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteFreeCompactComposition` | P8 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteFreeSystemRestriction` | H3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteGammaEvaluationIsIso` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteIndHeartAdjunction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteOrientationReduction` | E3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteProductCompactification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteProductOpenRestrictionPasting` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteProductOrdinaryNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteReductionOfPurity` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteTripleProductDefinitions` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteTripleProductNormalForms` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FiniteWeilIndPushExact` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FixedPairTruncationCohomology` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ForwardProductCoordinateTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FourierKernelConvolution` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.FourierTraceFormula` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.GeneralCondensedWeilRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.GlobalIdentityNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDuality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.GlobalVerdierDualityData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.HomChainPairingNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionBijection` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionReconstruction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralAdjunctionSourceComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralCompositorLimitRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralDirectImageTower` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralOrientationReductionInjectivity` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralOrientationShiftedSheafModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisonData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralReconstructionComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralScalarIsomorphismExchange` | H5 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralSmoothAdjunctionPresentation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.IntegralTowerProjectionMates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.LisseDenseOpenRecovery` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.LisseExtensionInertia` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.LisseShortComplexCommonStageExactness` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.LocalizedTopChern` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MiddleExtensionHcZero` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MiddleExtensionSectionRestriction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCompactSupportExchangeData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientChange` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupCoefficientSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupFieldCoordinates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupFieldNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupFieldOperations` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupOperationComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupRingedNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupTensorClosure` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupTensorComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupTensorElementary` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.MixedCupTensorNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ModelAffineIntegrationOrientation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ModelChartOrientationAssembly` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ModelOrientationChartDescent` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ModelOrientationSourceNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ModelOrientationTateDetection` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.NativeGeometricBrownConstructibleComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.NativeProperCoefficientOperations` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.NativeProperTensorComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarCounitCategories` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarCounitData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.NativeWeilScalarFrobeniusCounit` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.NormalizedIntegralPurityTrace` | X3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.OrderedLineLevelBounds` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.OrderedTowerOrientation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.OrientationGroundFieldRetagging` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PfRefinementCompatibility` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PodCtfAdjunctions` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PodCtfPairingMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PodHomChainCounitFormula` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PodHomChainCtfDomains` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PodHomChainUncurriedTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PointFrobeniusTransportNormalization` | G7 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PointWeilPairingCoordinates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PointWeilPairingRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PointWeilTensorRepresentatives` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PointWeilTransportUnitShift` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProEtaleCtfPullbackDomains` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductCompositionCoordinateComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductExchangeCoordinateDefinitions` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductExchangeCounitCoordinates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductHorizontalExchangeFactorization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductOpenAdjunctionNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductOpenCounitNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductOpenSupportNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjection` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProductOpenTensorProjectionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCoherence` | V5 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProjectionReductionPresentation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurAdicReconstruction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurCoordinateRepresentingFamily` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPair` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralRepresentingPairData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportComparisonData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportDerivedComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurIntegralSupportOrdinaryComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurRepresentingPairFiniteScalar` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurSupportPresentationAlpha` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityConjugatesTowerReduction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityFiniteReductionTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityPullbackLevelBounds` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityPullbackReductionTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityTensorMapNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityTowerReductionComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.PurityWitnessedMateNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RamifiedScalarSystemTranspose` | B4 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalExceptionalFinalEquations` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalPurityCoherenceDescent` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalPurityComparisonDescent` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalPurityScalarLocalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalPuritySourceLocalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalScalarComparisonIdentification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalStalkExact` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RationalizedSmoothAdjunctionDiagrams` | J1 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ReconstructedBrownMateLaws` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementCoherence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ReconstructedPairRefinementData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ReconstructedRefinementCommon` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ReconstructedRefinementSingleDegree` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ReconstructedRefinementTraceSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ReconstructedRefinementTraceTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ReducedFrontierMixedGluing` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RefinementFiniteOriginEvaluation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RelativeKunneth` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RelativeKunnethCubeFactorTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RelativeProductBaseChangeFactorSquares` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ResidueCompatiblePullbackFrobenius` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.RetaggingCoefficientTowerTransfer` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` | K3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SemilinearCompactifiedGraphEvaluation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfCoefficientComparisonConclusions` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfLocalizationAllStages` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfNormalizedCommonStageWeilSquares` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfNormalizedRationalClosedComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfNormalizedRationalWeilSquares` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfOpenClosedTriangleAllStages` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfPackageExceptionalCoherenceRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfPackageLocalizationProjectionRealization` | F2 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SfRecollementReductionBoundary` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothOperationCoefficientModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothOperationDescentSpecification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothOperationIdentificationSpecification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateCategories` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateChartModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateComposition` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateFoundations` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateProjectionModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateRightComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityCoordinateTensorComparisons` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityFieldExtension` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerBinaryCounitRepresentability` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerChartAdjunctionLevels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCompatibleCounitLift` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGamma` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGammaData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGlobalChartAdjunction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGluing` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerGluingData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerOpenHomComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SmoothPurityTowerRestrictedRepresentingPair` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemClopenMateIdentification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemCompatibleCompositorData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemCompatibleCompositorNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemCompositorFiniteWordEvaluation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemCompositorRefinementSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemProjectionChangeCompatibility` | X7 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaCoherence` | H9 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemProjectionFormulaMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemProjectionTriangleCompatibility` | B3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemProperOpenInvertibility` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemRefinementConstructibleDomain` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemScalarBasisDistributivity` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemScalarProjectionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemScalarProjectionIdentification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemScalarRefinementRestriction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemScalarTensorConstituents` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationCoreExistence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemTensorPresentationIdentification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.SystemTensorSemilinearRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TensorHomCoefficientTransposes` | P3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TensorHomExchange` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TensorMapPresentationIndependent` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TensorMateInvertibleInput` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TensorTransposeFiniteEvaluation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TensorTransposeTowerNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerAdjointCompositorRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerCompositorFiniteEvaluation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerNormalizationPreservation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerPurityAdjointTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerPurityRealizedTranspose` | D3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerTensorAdjointDomains` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeEvaluation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TowerTensorTransposeWords` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCartier` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCoprojection` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionCore` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionOrdinary` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionProjective` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedCoordinateSectionSign` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicAgreement` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackAdicIdentification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCanonicalShifts` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackCoefficientCoherence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcCoordinates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcPullback` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackPbcTwist` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarFamilies` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarPrimitives` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackScalarShifts` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackShiftCoherence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareCoordinates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareScalars` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackSquareShiftEquations` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerBounds` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomain` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerDomainDefinitions` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.TwistedPullbackTowerOrigins` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.UniformTowerTensorClosure` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThom` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThomMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VectorBundleThomProduct` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VerdierCoefficientRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VerdierHomChainComposition` | Q6 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VerdierHomChainCompositionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VerdierOrdinaryTensorTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.VerdierProjectionExceptionalPaste` | A4 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilBaseChangeSemilinearPasting` | T2 | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchange` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilChosenDualityExchangeData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilChosenExchangeConstruction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilChosenTransposeNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilFourierInversion` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilFourierPlancherel` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilOpenImageDelta` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilPullbackFibreReturn` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilPullbackLocalFrobenius` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlCanonicalImmersionCohomology` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlFrameworkOpenExchange` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenComparisonData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlImmersionPullbackWeightPreservation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlOpenDiagramComparisonTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlOpenWeilUnitEmptyFibre` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlWeilHeartLocalizationExact` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.Paper.ZlWeilShriekCoefficientLongExact` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.NestedAffineOrientation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SecSmoothPurity.SmoothPurityNaturality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.AmbientAdjunctionCompositorNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.AmbientExactClopenComparison` | R4 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.AmbientProperOpenPasting` | H4 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.AmbientUnderivedClopenPasting` | S1 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CanonicalOpenReductionIsIso` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CanonicalReductionPullComposition` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CartesianCompactSupportCompositor` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeDomains` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangePaths` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedProjectionExchangeSystem` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedShriekCompositionLaws` | C4 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompletedTensorSlotShiftLaws` | F4 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.CompositionProjectionMate` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ConstantSemilinearGeneratorComparison` | G5 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ConstructibleReductionGood` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ExceptionalIntegralReconstruction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.FiniteReductionCompletionUnit` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.FiniteTorOrdinaryPullComplete` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.FiniteTorOrdinaryTensorComplete` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.GeneratorReductionStatement` | F1 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralBasicRealizationData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralCanonicalAmbientModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationBridgeWords` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationComparisonBridge` | S4 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationOrdinaryScalarAction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationRealizationData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralComparisonRecursionLaws` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralConstantCompleteTransport` | G2 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionCoefficientSquares` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralExpressionRecursion` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralNormalizedRefinementPasting` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralOpenMateNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | X6 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralProperTowerTransition` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationAssemblyData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralRealizationRecursion` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralReductionPullbackModel` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralSupportTowerNormalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.KunnethSecondOpenSubstitution` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenBaseChangeReductionSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCoefficient` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateCompletion` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateDescent` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateFinite` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateIntegral` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenClosedWeilMateStructures` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenDvrRingedIdentification` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenInterchangeReductionSquares` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenReconstructionEffectivity` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenReductionMateLocalization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenSupportStepBounds` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OpenTensorReductionSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryOpenReductionMate` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.OrdinaryProperOpenInvertibility` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.PrimitiveCompletionEffectivity` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.PrimitiveQuotientAugmentations` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProductNormalizationRealizationTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProductSystemUniformRealizationDomain` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProjectionIntegralCoherenceRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProjectionRefinementDescent` | E2 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProjectionSystemCoherence` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenLambdaReductionSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | J3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ProperSupportStepBounds` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.PullQuotientAugmentationOnGood` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.RamifiedScalarExceptionalLimit` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.RefinementProjectionCounit` | T3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SemilinearEvaluationDerivedAdjunction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SemilinearEvaluationOrdinaryAdjunction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SemilinearEvaluationRingSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ShortWordIntegralDomain` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.StrictCompactificationProjectionShift` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SupportedWeilMateLift` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenScalarSquare` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemProperOpenSupport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemPushCompositionLaws` | C3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.SystemTensorShiftRepresentativeModels` | G3 | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.TensorAdjunctionReductionSquares` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.TensorQuotientAugmentationOnGood` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.ThreeCellCompositor` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionCompositorContraction` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionNormalForm` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SixFunctors.TriangleProjectionSystemNormalForm` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryBinaryProductTranspose` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryProductTransposeData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryTripleLeftComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryTripleProductTranspose` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.SmoothPurity.OrdinaryTripleRightComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.DualRealizationComparison` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.NativeBidualEvaluationRealization` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.NativeDualRealizationComparisonData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetful` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalForgetfulData` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalLeftModels` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalPointUnit` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.NativeExceptionalStructuralTransport` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.NativeSectionClosedForgetful` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.OrdinaryClosedPresentation` | unclaimed | Same public declarations and definitions; no adaptation. |
| `Sheaf.WeilSheaf.StructuralOmegaHomPairs` | unclaimed | Same public declarations and definitions; no adaptation. |

## Status

landed 20261026T071149-L-3873007 2026-10-26 (merge of deliver/U1/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
