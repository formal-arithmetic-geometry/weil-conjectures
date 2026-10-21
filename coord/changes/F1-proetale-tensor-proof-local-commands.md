# ProEtaleInverseImageTensorComparison proof-local commands

## Reason

Record the commands added while proving all nine original theorem holes. The stage-3
interface scanner conservatively classifies section/universe commands and local
attributes as an interface change. All original public signatures, public imports,
and definition bodies remain unchanged. The added helpers are private and proved.
No public instance, notation, simp attribute or declaration is added.

The local irreducibility attributes prevent repeated expansion of the small-model
inverse image, adjoint conjugations and tensor/sheafification constructions. Proofs
instead use their proved unit and normalization equations. The complete module
compiled in 52.5 seconds at the unchanged 60-second limit; subsequent delivery
attempts also completed compilation and axiom checks before packet preflight.

## Old

The original file opened the following context, with no local irreducibility commands
and no private generic-helper sections:

```lean
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SheafOfModules
namespace AlgebraicGeometry.ProEtaleTensorComparison
```

## New

The original context stays. Private helper sections introduce explicitly bound site,
hom and coefficient universes. Their names are TensorPairing, IdentityScalars,
AlgebraicLift, TensorPresentation and ScalarFunctor. Every section is closed.
The ChangeOfRings scope is opened only inside IdentityScalars. Scoped heartbeat
options are confined to the four expensive constructions and do not change the
server wall-clock limit. Added irreducibility attributes, all local, are:

```lean
attribute [local irreducible] proEtaleModuleInverseImage inverseSection
attribute [local irreducible] ringComp
attribute [local irreducible] Functor.sheafPullbackConstruction.sheafPullback
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
  AlgebraicGeometry.ProEtale.setPullback
  AlgebraicGeometry.ProEtale.setPullbackAdjunction
  AlgebraicGeometry.ProEtale.setPullbackComp
attribute [local irreducible] ringId
attribute [local irreducible] monoidalCategory tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction
```

These attributes expire with the namespace/file scope and do not affect importers.
The private algebraic lift explicitly constructs the recorded module inverse image
with its normalized underlying-set identification and proved operation graphs.
It does not occur in any public definition body or public signature.

## Users

The downstream source scan found 623 transitive consumers. All are listed
below. No consumer source is changed, so no adaptation claim or forced adaptation is
involved. The holder column is marked not applicable because there is no edit to
that module; holders retain their work. Public data and theorem signatures are
preserved, and the newly scoped commands have no downstream semantic effect.
The maintainer's independent reader and global build check the unchanged consumers.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison | F1 | Nine theorem holes proved; private proof commands only. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CoefficientMateDiagonalGraph | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.OpenExtensionRHomContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleClosedUnderivedProjection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleConstantScalarPullbackCube | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackIdentity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleDirectImageGlobalEvaluation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleRingRestrictionSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.RelativeSingleTensorCohomology | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.ScalarPresentationCokernel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.SemilinearAlphaPullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.SemilinearCompositorCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.SupportedBottomGluing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.TorsionLineSystemBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianComparisonLiftRelabelling | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingCartesianLiftPullbackEquivalence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowEvaluation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenArrowFactors | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingClopenSectionEvaluation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenBaseChangeEvaluation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingOpenUnitCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingOrdinaryClopenEvaluation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingPullbackUnitCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingTensorComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.AlgebraicGeometry.VaryingRingTensorSupport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Compactification.NagataDensityNormalizationSheaves | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.FieldTheory.CondensedSubfieldBasis | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AdicFiniteExchangeEncoding | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AdicNormalizedFibreExactness | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AdicPunctualWeights | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AdicSmoothBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AdmissibleScalarRealizationExact | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AffineLineInvariance | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.AmbientCompleteRawSystem | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.BoundaryOrdinaryImages | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.BoundedConstructibleBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.BoundedExchangeAmbient | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.BoundedFiniteModelGeneration | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CartesianCoefficientTwists | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CartesianCoefficients | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ClopenStrictSystemComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ClosedSupportBoundedContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ClosedSupportedCupVanishing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientFiniteDescentHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientHeart | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientHeartClosure | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientHeartFiltration | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientHeartGeneration | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientHeartTriangulated | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientProjectionSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoefficientPushFilteredLegs | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CoherentRationalPullbackIdentity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CohomologyTorInterval | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CommonStagePullbackIdentity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CommonStageWeilLinearDual | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompactSupportCoefficientAction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompactSupportFiniteAction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompactSupportReductionTower | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompactSupportReductionTowerConstruction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompleteCompactSupportProetale | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompleteProetale | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedBaseChangeMap | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedCompactSupportExchange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedDirectImageLimits | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedExchangeCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedFiniteExchangeCoordinates | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedMapReduction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedPerfectScalarPullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedProjectionCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedPullbackTensorComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedPullbackUnitTower | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedReductionPullbackSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedReductionSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedRingStrictFiniteExchange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedScalarUnitAdjunction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedTowerCompatibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletedTowerCorners | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CompletionTriangleComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedBoundedHomContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedCompactSupportProjection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedConstructibleOneStep | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedERealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedFiniteModelExtensions | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedFinitePresentationDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedLocalizationHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedOpenClosedRecollement | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedPointCoefficients | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedQbarComparisons | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedSheafExtContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedStratumModelAssembly | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedStratumModelInductionStep | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.CondensedTateRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstantPerfectQuotientProjection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstantTowerDirectImageNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstantWeilStructure | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstructiblePullbackTExact | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstructibleRationalHomComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ConstructibleTruncations | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousCoefficientFreeRank | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralComparisons | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralLocalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralPullComposition | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralPushComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLissePullbackSystem | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousLisseStratumDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousQbarConstructibleGenerators | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedExchangeExactNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedGeometricStalk | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedNakayama | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedNakayamaResolution | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedOpenSquareRestriction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DerivedPullbackTensorIso | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DiagonalTowerSystem | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DirectImageChangeRingTranspose | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DirectImagesConstructible | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.EffectiveComparisonRealizationModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.EtaleProEtaleCoefficientTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ExplicitExceptionalPreservation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FdCoefficientComparisonSystem | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FdCommonStageComparisonDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FdCompletionInverseScalarCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FdPullbackComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FieldStageOrdinaryRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FieldTorAmplitude | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FieldTwistInverse | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCoefficientModelComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteConstantModelResolution | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteEncodingCompactification | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteEncodingNaturality | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteEncodingTensorTor | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEncoding | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteForwardProductSymmetry | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteModelStratumFiltration | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteProjectionActionLaws | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteProperBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteProperProductTranspose | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteReductionExchangeRectangle | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteReductionPullbackSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteRingSectionDeformation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothPurityMaps | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteStageRationalExchangeCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FormalClosedSupportDerived | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FormalClosedSupportSheaves | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FourierArtinSchreierProperties | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FourierTraceFunctions | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.FrobeniusFixedPairComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralBoundedStratumBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralCoefficientExtComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralCoherenceTower | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralComparisonRealizationModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralCompositionCounitImages | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralConstantModelHeart | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralConstructibleHeart | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralConstructibleSheafHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralCriterionReductions | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralDerivedCoefficientData | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralHeartDualizable | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralHeartLocalModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralHeartRealizationExact | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralHeartResidueDual | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralLocalizationHomColimit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralModelOpenClosedPieces | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralModelsOperations | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralProperReductionBound | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralProperReductionModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralPullbackComposition | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralPullbackReductionCounit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralPullbackSystemComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralResidueClassTriangleClosure | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralResidueExchange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralStratumHomFormula | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralTensorPullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralTensorShriek | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralTowerLimitComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralTwistBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralTwistDerivedScalar | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralTwistScalarCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IntegralWindowCoproductComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.InternalHomDualConstructibleModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IsomorphismDerivedPullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IsomorphismReductionTower | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IsomorphismScalarAugmentationCone | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IsomorphismScalarComparisonAgreement | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.IsomorphismScalarTensorKFlatModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.KummerAdditivity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LatticePullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LatticeSubquotientFiltration | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LisseLatticeReducedOpen | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LocalFrobeniusTrace | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LocalModelTorBoundDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LocalizedDirectImageComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.MixedReductionUnit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ModuleDerivedCompositorCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.NormalProEtaleMonodromy | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.NormalizedCoefficientFamilies | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.NormalizedPullbackCompositionTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.NormedCoefficientRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.OpenFiltrationSuccessor | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PadicIntegersInvertEll | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PbcConstructibleReductionPullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PbcQbarCompletedPullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PointAutomorphismTransportScalarExtension | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PointExactDerivedModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PointRealizationCoefficientComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PointTransformationCoefficientDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PrincipalReductionConeCalculus | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProEtaleConstantReductionModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProEtaleConstantReductionTower | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProEtaleScalarMateNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProEtaleTateTwists | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProjectionSectionNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProperEtaleOriginScalarIsomorphism | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProperHeartBoundReduction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ProperUnboundedWindowBounded | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PullbackIdentitiesScalarExtension | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PulledReductionNormalizationComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PulledReductionStrictTowerComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PunctualSpectrumExactFibre | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurInverseImageTensorComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurInverseImageTensorHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityConventions | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityExteriorProductFrame | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityFiniteKummerDefinitions | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityFiniteKummerLevel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityFiniteOpenIntervalDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityGeneralAdmissibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityKummerNormalizedBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityKummerNormalizedProjection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.PurityKummerRootTensorBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QbarCurveOrdinaryImage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QbarTwistCommonStage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QlbarDirectImageComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QuotientExpressionKFlatNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.QuotientSystemMixedCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalCoefficientCategoryComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalLocalizedHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalModuleRealizationFunctor | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalRealizationFiniteConeModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalRealizationPullbackComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalRealizationScalarCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalRealizationTensorComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RationalStratumIntegralModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RealizationAdjointComparisons | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RealizationCompletedPull | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RealizationLocalizedPush | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RealizationScalarFunctor | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ResidueLisseProjectiveModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RestrictedScalarCoefficientLocalConstancy | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RestrictedScalarCohomologyLocalConstancy | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.RestrictedScalarTensorCohomologyComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SbcCompletedOperations | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ScalarExtensionTensorUnit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.ScalarModelImmersionExtension | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SectionDerivedRealization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SectionDerivedTensorData | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SectionDerivedTensorNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SectionModuleOperationsData | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SemilinearCompactSupportCoefficientTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfCbcDirectImageReductionUnit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfCommonStageWeilCohomology | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfCompletedPullbackMateFactorization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfExactPullbackCounitNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfExchanges | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfLocalizationAllStages | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfOpenReductionAdjunctionTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SignedTateCoefficientExponentNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SiteComparisonEdgeSection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SmoothPurityTowerReconstruction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StratifiedConstantModelProductBound | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StratifiedDualizableBounded | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StratifiedDualizableHomContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StratifiedLattice | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StratifiedLatticeRank | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StratumScalarExtension | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StrictQuotientExpressions | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SupportedExteriorClasses | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.SystemTensorMateArrows | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TAdmissibleCoefficientModels | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TameBoundaryScalarComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TateInverseLimitBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TateTwistLisseLine | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TateTwistLocallyFree | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TraceBaseChangeFirst | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TwistPreservesFiniteness | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.TwoTermReductionCohomology | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.VectorBundlePurity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.WeilCompactSupportCohomology | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.WeilComplexTraceFunction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.WeilGenericLissity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Paper.WeilIndSheafCategory | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.ConstantScalarPullbackSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.DirectImageScalarExchange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.DirectImageScalarOperations | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.OpenScalarExchange | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.OrdinaryRestrictionPullbackSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.ProEtaleDirectImageScalarCocycle | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.ProEtaleOpenScalarCocycle | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.ProEtaleScalarTensorNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.ReductionDirectImageComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.ScalarExtensionFunctor | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SecSmoothPurity.TensorPullbackSquare | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.BrownHypothesesSmall | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.CompactSupportProperImageTower | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.FieldTensor | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.FrobeniusPointTransport | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.IntegralExpressionOccurrences | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.IntegralModelsGenerators | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.IntegralSystemExpressionDomain | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.IntegralSystemOperations | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.OpenFactorPullModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.OpenFactorTensorModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.OpenRoosUnitAdjunction | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.OpenScalarTensorNormalization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.ScalarSixPullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Targets.PoincareTateBoundedConstructible | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Topology.ProfiniteCondensedRing | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Topology.ProfiniteSectionsFiniteQuotient | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.Topology.TopologicalModuleCondensation | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.TraceFormula.CondensedStalkFrobeniusOrbitTrace | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.TraceFormula.IntegralComparisonCounitCharacterization | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.TraceFormula.IsomorphismMultiplicationConeDescent | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.TraceFormula.PointTransportComposition | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | Not applicable: no adaptation | Same public API and data; no source edit. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | Not applicable: no adaptation | Same public API and data; no source edit. |
| TargetsCheck | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.WeilObject.BoundedConstructible.Homology | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | Not applicable: no adaptation | Same public API and data; no source edit. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | Not applicable: no adaptation | Same public API and data; no source edit. |

## Status

landed 20261021T193149-L-938028 2026-10-21 (merge of deliver/F1/Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison)
