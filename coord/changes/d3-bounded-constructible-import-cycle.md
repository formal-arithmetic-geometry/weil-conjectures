# CondensedFieldContinuousRealization public imports and consumer repairs

## Reason

The existing public import of `MorphismDefs` makes the constructible Serre API import the
bounded-constructible restricted-functor module back through the base-change definitions.
This prevents using its proved Serre theorems to prove tensor preservation. The realization
module needs the basic module-object pullback API, and its consumers also need
`CondensedRing.upperStar`, `upperStarComp`, the finite-presentation/free-module API,
and the localization restriction adjunction/comparison API.
Replacing this import by `UpperLowerStar.Defs`, `ConstructibleSheaf.ProEtaleModule.Def`,
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`,
and `ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
retains those exports and removes that cycle. The module is unclaimed. No declaration signature, definition, proof,
visibility attribute or target statement changes.

The earlier review of B2 found that the import-pruning check additionally found
`constructible_of_iso` from `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`
used in the tensor delivery’s Serre-closure consumers. The realization module retains that public export with a direct
public import of the defining pullback module, preserving the consumer API without the
base-change cycle. Each listed consumer also imports that defining module directly and privately.
The triangulation consumer is a new module of this delivery; the existing Paper modules
were unclaimed when edited and receive only the additional import. Their signatures, visibility and proofs are unchanged.

The subsequent review found that two more unclaimed consumers require direct imports.
`Sheaf.Paper.ContinuousModuleEncodingScalarExtension` receives the private import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`;
`Sheaf.PoincareDuality.CompatiblePrimitiveRoots` receives the public import
`WeilConjectures.AlgebraicGeometry.Sites.Kummer`, which supplies its public root-system
definition. The roots adaptation adds Kummer publicly and also imports
`WeilConjectures.Mathlib.AlgebraicGeometry.Limits` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Restrict` privately. The latter two provide
`Scheme.isEmpty_of_subsingleton_Γ` and `Scheme.isUnit_ι_appTop_basicOpen`, whose absence
was detected when compiling its unchanged proof bodies against the reduced dependency
closure. No other line in the roots module changes. The
scalar-extension module additionally renames its private helper `tensorHomEquiv` to
`scalarExtensionTensorHomEquiv` and updates its one use. The required import brings the
public `SheafOfModules.tensorHomEquiv` into scope, and Lean otherwise reports
"a non-private declaration `SheafOfModules.tensorHomEquiv` has already been declared".
The helper type/body and all public signatures and visibility attributes are unchanged.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
```

The scalar-extension private helper was originally declared as:

```lean
private noncomputable def tensorHomEquiv
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    (changeOfRings α M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :=
```

## New

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
```

The scalar-extension helper retains the same type and body under its fresh private name:

```lean
private noncomputable def scalarExtensionTensorHomEquiv
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :
    (changeOfRings α M ⟶ N) ≃
      (M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj N) :=
```

Its only caller uses `let e := scalarExtensionTensorHomEquiv α`.

## Users

Current source scan: `python3 tools/downstream.py
Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization --uses constructible_of_iso`.
The table includes all transitive consumers and each adapted module. The existing
adaptations were unclaimed at the time of editing. Their public signatures and visibility
are preserved. Every changed file compiles individually; the direct-consumer checks and
final dry run are recorded in report.md. This is restoration of the earlier reviewed
import repair, rather than an unrelated API expansion.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.BoundedConstructibleTensorSingle | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.ClosedSupportStratumHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Replace the public MorphismDefs import by the four defining API imports; mathematical definitions and public signatures unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | X2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | C8 | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | D4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FiniteRingSiteTensorTranspose | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FullCdAmbientAdjoint | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.GraphFrobeniusUnitComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.LfpTensorSingle | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.LocallyFreeTensorSingle | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | E6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProEtaleOpenInjectiveProperAcyclic | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProperExceptionalOpenBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | W8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.ProperOpenDerivedSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | X7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.RelativeAdjointOpenOrigin | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison | S1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.SfConstructibleExceptionalAdjointDischarge | E7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.AlgebraicGeometry.SiteClosedCounitTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalBase | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalProjection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalProjectionData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicExceptionalScalars | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicSectionClosedSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AffineCurveHcZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AffineSpaceRationalInduction | Q2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ArbitraryFieldAdjunctionScalars | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BasicOperationsCoefficientReduction | K2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryDualizingComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryProEtaleProjectionComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryProEtaleQCompatibility | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryQFoundation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryQMaps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundaryQTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BrownExceptionalAdjoint | T6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CanonicalWeilFundamentalRepresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CartesianCoefficientTwists | Z6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | E2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ClopenStrictSystemComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ClosedAdjointConstructibleYoneda | M1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ClosedSupportConstructible | N4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefTowerCoaugmentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientFiniteDescentLisse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | U5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeart | X8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartCommonStratification | F2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartFiltration | P4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartGeneration | P7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartSmall | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CohomologicalSmoothComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CohomologicalSmoothnessTheorem | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageCompactWeilCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CommonStageWeilShriek | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportCoefficientAction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportFiniteAction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportFiniteFieldIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportPerfectness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportReductionTower | P2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactificationCoherenceCocycle | R4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactificationLocalizing | F4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompactificationRefinementLocalizing | H3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CompletedStalkReparametrizationCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedERealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CondensedZlReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConnectedConstantH0 | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstantExtensionWeilHeartEquivalence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Add only a private direct pullback import for constructible_of_iso. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleCompactnessBounded | R4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleDegreeZeroProperSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleHomComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | R2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ConstructibleSingleDegreeComparison | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Add private MonoidalClosed import; rename the colliding private helper and its one caller, with unchanged type and body. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | N4 | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.CoprojectionCompositionMate | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DegreeZeroCompactSupportSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | T2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DerivedTruncationCoproducts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DetThmSfCtfStabilityInternalHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DiagonalTowerLimit | G3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DiagonalTowerSystem | W6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DirectImageChangeRingTranspose | J2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DirectImagesConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DlConstructibleFibresExact | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | R2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitude | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleProEtaleAdjunctionTransfer | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleRhoMonoidalMate | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.EtaleWeilFundamentalRepresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EtaleWeilSheafEquivalence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalDerivedSiteRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalFiniteRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalFiniteSupportRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalInverseImageExistence | U1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalProEtaleRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExceptionalSiteRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FieldShriekLowerBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteBoundaryWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteClopenExceptionalRestriction | C2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientAdjointComparisons | F3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientHomChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | G9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteConstructibleHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteEtaleDescent | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.FiniteLocalizingExceptionalPreservation | Q7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteProductCompactification | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteProperLocalizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | W2 | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteStageVerdierBiduality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteTorStability | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteWindow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteWindowBounded | C1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FiniteWindowUnbounded | C7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FixedStalkIdentificationReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FormalClosedSupport | Q9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FourierKernelConvolution | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusCoefficientReductionCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | V8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusExchangeDegreeZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusGeometricExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusOperatorCompactDescription | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusPullbackComparisonCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GlobalGeometricFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCompactSupportPrescribedReductions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralCompactTransportSystemMatePasting | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstantModelHeart | C2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.IntegralConstructibleCompactness | E7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleHeart | P1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleInternalHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Add only a private direct pullback import for constructible_of_iso. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralCriterionReductions | X3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralExceptionalInverseImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralHeartDualizable | C5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralHeartLocalModel | C3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralLocalizingProperBaseChange | H2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralModels | D4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralModelsOperations | N1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralOpenImageProperFormulas | R8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralPointTransportTowerPowers | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralProperBaseChange | B4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralProperDirectSums | F5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralProperProjectionFormula | W9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Paper.IntegralStratumExtBound | K1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralStratumHomFormula | Y9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTensorProduct | N3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTensorPullback | J2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTensorShriek | F2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTwistBaseChange | J4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IntegralTwistScalarCoherence | N4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.InterchangeProperPasting | S4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.InternalHomPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IteratedWeilCocycle | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.IteratedWeilMap | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.KummerAdditivity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | H8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LisseFiniteCoefficientModel | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.LisseFiniteHomLift | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalFrobeniusConjugacy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalFrobeniusTransportNormalization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | H9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.LocalizingLowerShriekComposition | A4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.MateOpenRestriction | U2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.MixedReductionUnit | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ModelCompactComparisonUnit | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | W5 | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | B3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OpenCompactSupportFiniteTor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.OpenImmersionLocalizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OrdinaryCompactCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.OrdinaryCompactWeilCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PoincarePointFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PointCompletedEvaluation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleInternalHomFiniteTorConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtalePerfectHomTorAmplitude | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleProperOpenInterchange | X6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | D2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperBaseChangeRational | E9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperCoincidenceFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperCompactCoincidence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperExceptionalRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartBoundLattice | G2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartBoundReduction | Y5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartBoundTorsion | J4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperHeartConstructibleCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperIndConstructibleBoundedBelow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperIndConstructibleUnbounded | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedCoproductComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedCoproducts | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedWindow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperUnboundedWindowIso | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurAdicReconstruction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | Y2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityAffineLineOrientation | J6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityAffineLineOrientationUniqueness | E2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityChernClasses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityConventions | X8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityCoprojection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | R2 | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDncComparisons | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | E3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityGysinStructure | F1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PuritySourceTransports | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarAffineSupportBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarDerivedDirectImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarOrdinaryAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QcqsCompactSupportRealization | D3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalExceptionalRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | Z5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalRestrictionGlue | R9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalStalkExact | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RealBoundaryPathIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RealSheafSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RelativeSupportBottomDescent | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RelativeSupportCoordinateModel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RestrictionLocal | R3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfBidualityClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfOpenClosedTriangleAllStages | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfPreservationClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SfProEtaleProjectionFormula | X7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothExceptionalBaseChangeStatement | M9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothLisseIntegralLattice | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothMateCounitCancellation | G4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityQbar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerBound | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothPurityTowerShriekLevels | S6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothTrace | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.StratifiedLattice | M6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TateTwistLocallyFree | S7 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TensorTraceTranspose | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TowerCompactSupportProjectionFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceBaseChangeFirst | E1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceBaseChangeSecond | E4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceCohomologicalCorrespondence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceCompactificationCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFixedScheme | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaAdicSystem | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaCoefficientConventions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaCurveIntegralLattice | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaDualizingComplex | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaLocalFrobeniusOperator | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaStrictWeilComplex | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TraceTransposeBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TrfDevissageGeneration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TrfWitnessedOpenPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TwConventions | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TwFrobeniusAction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.TwistPreservesFiniteness | G5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UnboundedBaseChangeExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UnboundedLocalizingPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UniformConstructibleExtIntegral | K4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UniformConstructibleExtRational | E3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.UniformConstructibleExtTorsion | M4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VaryingRingGraphSummand | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VerdierExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilCompactSupportCohomology | A8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilFourierInversion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilOne | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilPullbackLocalFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.WfTensorCompletionFrobenius | U8 | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.ZlFiniteAdicDirectImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | unclaimed | Add public Kummer and private Limits/Restrict imports required by unchanged definitions and proofs. |
| Sheaf.PoincareDuality.IntegralResidueLimit | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.PoincareDuality.IntegralTateBasis | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | C3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.EtaleCoprojectionRhoCompatibility | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | U9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.MixedBaseChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ProEtaleFiniteCDProperOpenInterchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ReductionDirectImage | F1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ReductionExceptional | G8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.RestrictionTransitionTranspose | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | G1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | N2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | M1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Z9 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefQbarVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefTowerEvaluationPairing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CoefTowerTraceRectification | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CompactCoefficientComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CompositionProjectionMate | V5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.DetSfCompCompositionBaseChange | H6 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FieldTensor | N1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteDualitySiteComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteDualizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | E3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FrobeniusFixedPoints | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.GeneratorReductionStatement | N3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.GraphFrobeniusOpenExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.GraphFrobeniusPointExchange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralBasicOperationShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralBrownAdjoint | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralCompactificationSystemRealization | W8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | B8 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralLocalizingCompactSupport | T2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralModelsGenerators | T3 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRealizationRecursion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRealizationShiftCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionGlue | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralSystemOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | T4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.IntegralVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.InternalHomPullback | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenAdjunctionShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | F4 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.SixFunctors.ProperImageLocalizingProper | K2 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ProperOpenProjectionMate | X5 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.RationalVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SelectedSchemeGaloisComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SynchronizedCanonicalMaps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SystemPrimitiveComparisonShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | H1 | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| Sheaf.Targets.AffineSpaceRationalLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Targets.PoincareUncurry | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.TraceFormula.CompactFrobeniusTransportComposition | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| TargetsCheck | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.AdditiveCharacters | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusTransport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocalMonodromyFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.AlgebraicGeometry.FundamentalGroup.TameInertia | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Boundary | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryInertia | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Curve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightExterior | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationData | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationDual | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPath | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathGeometric | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.FourierTransform.Perverse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.PoincareDuality.ProjectionFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.PoincareDuality.Verdier | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.Statement | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.TraceFormula.Basic | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.TraceFormula.Statement | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Definitions, statements and target meanings unchanged; only transitive import provenance changes. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.HomologyShift | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| module | unclaimed | effect |

| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.RealSheavesCohomologyEulerSeries | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.AmbientProperOpenPasting | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.SchemeGaloisCoefficientChange | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |

| Sheaf.Paper.FiniteRegularReductionDualizing | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.ProperSectionsSemilinearGerms | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.CompositionProjectionMate | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | unclaimed | No source adaptation; existing declarations unchanged; transitive dependency only. |

| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.A1FiniteWeilSectionsDecomposition | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.ConstructibleSingleDegreeComparison | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.ContinuousQbarExceptionalPreservation | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.EtaleSectionDeformationComparison | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.IntegralConstantModelHeartClosure | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.LisseFiniteCoefficientModel | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.LisseFiniteHomLift | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.TwistFrobeniusScalar | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.Paper.WfTensorCompletionFrobenius | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineChart | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralExceptionalAffineFactorization | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionBoundedDescent | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionChartCover | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.IntegralRestrictionCohomologyDescent | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Transitive consumer; defining imports and public signatures unchanged. |

## Status

landed 20261019T093325-L-2295338 2026-10-19 (merge of deliver/D3/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible)
