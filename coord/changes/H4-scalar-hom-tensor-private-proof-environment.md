# CategoryTheory.scalarHomTensorCoherence private proof environment

## Reason

The completed proof uses general private diagram lemmas, termwise component APIs,
and local instance and irreducibility attributes to avoid repeatedly unfolding
tensor and derived-category constructions. The delivery preflight requires this
administrative record because its conservative command scan flags new attributes,
variables, universes and sections as changes to what importers see.

Every public declaration signature, public import and public definition is
unchanged. The sole public theorem now has a complete proof. All new definitions
and helpers are private and proved; no attribute is global. No target meaning
changes. All data remain actual canonical constructions, with no new choice of
an object from an unproved mere-existence statement.

## Old

The original file's elaboration commands are verbatim:

```lean
set_option autoImplicit false

set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency.types true

universe c v r w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

open WeilConjectures SheafOfModules CategoryTheory.Functor

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local irreducible] monoidalCategory
```

The public `CategoryTheory.scalarHomTensorCoherence` theorem has the exact
signature retained in the delivered file and ended in `by sorry`. Its original
private proof-only helpers were `total_pure_hom_ext`, `complexIso_unique`,
`tensorIso_unique` and `comparison_unique`.

## New

The delivered file's elaboration commands are verbatim:

```lean
set_option autoImplicit false

set_option backward.defeqAttrib.useBackward true

set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true

set_option backward.isDefEq.respectTransparency.types true

universe c v r w u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

open WeilConjectures SheafOfModules CategoryTheory.Functor

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

attribute [local irreducible] tensorCompRoute

attribute [local irreducible] tensorIdRoute

attribute [local irreducible] tensorIdRightRoute

attribute [local irreducible] monoidalCategory derivedInternalHomOfUniverses

attribute [local instance] isMonoidal_W_independentCoefficients
  preservesZeroMorphisms_curriedTensor_independentCoefficients
  preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local instance 2000] tensor_hasMap

attribute [local irreducible] coefficientTensorGenerator

attribute [local irreducible] ordinaryComp scalarHomOrdinaryRestrictionComp

attribute [local irreducible] complexCompIso

attribute [local irreducible] coefficientTotalTensor

set_option maxHeartbeats 800000 in

attribute [-instance] tensor_hasMap

attribute [local irreducible] eps epsRaw scalarPairComplexComparison

attribute [local irreducible] chainAdj

set_option backward.isDefEq.respectTransparency true in

set_option backward.isDefEq.respectTransparency.types true in

attribute [local irreducible] scalarHomExtensionComp

attribute [local irreducible] ordinaryId scalarHomOrdinaryRestrictionId

attribute [local irreducible] complexId

attribute [local irreducible] scalarHomExtensionId

attribute [local irreducible] modelIso
```

The additional universe `u` is used only by the private `tensor_hasMap` lemma;
the public theorem still quantifies its original universes `c v r w`.
The finite-(co)limit composition instances are scoped to
`section ExactRestrictionComposition`. The high-priority private total-tensor
instance is removed immediately after the chain-generator calculation.
All irreducibility attributes are local. The heartbeat setting is scoped to the
one dependent chain-generator proof; the compiler wall-time limit is unchanged.
The general private categorical and component lemmas are completely proved.

The three original unused private uniqueness helpers are removed; no external
consumer refers to them, and no existing public declaration is removed. This is
a proof-implementation replacement, not a public interface or statement repair.

## Users

The read-only `tools/downstream.py` query completed with
`--uses scalarHomTensorCoherence complexIso_unique tensorIso_unique comparison_unique`.
It reports 460 downstream modules and confirms that all three removed helper
names occur only in the item itself. A read-only import traversal supplies the
complete consumer table below, including those 460 consumers and the item. The only external named use of the public theorem is
`Sheaf.Algebra.Homology.ScalarInternalHomTowerCoherence`; its use is unchanged.
The other direct importer is `Sheaf.Algebra.Homology.ScalarHomComparisonTower`.
The removed helpers were private, have no external named uses, and cannot occur
in a public signature. No consumer requires adaptation. Holders are read from
current claim records at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.FlatInternalHomEvaluationRoof | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.InternalHomLocalizationComparison | G4 | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.ScalarHomComparisonTower | K1 | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.ScalarHomTensorCoherence | H4 | Completed proof; public API unchanged. |
| Sheaf.Algebra.Homology.ScalarInternalHomAdjunction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.ScalarInternalHomTowerCoherence | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.ScalarTensorComparisonTransport | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.ScalarTensorTowerComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.SemidualizingRHomConservative | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Algebra.Homology.SitePerfectScalarHomComparison | U6 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CartierKummerMap | Y2 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientMateDiagonalGraph | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization | X2 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductArrows | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CompactProductRealizationArrows | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | S1 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | A2 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | C1 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | S2 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.FiniteLevelPoincareDuality | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.Curve.KummerJacobianTateModule | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleClosedChartExceptionalPreservation | D3 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.FrobeniusFactorization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | C3 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.KunnethSupported | P9 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | R6 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.OpenModuleRestrictionIdentities | T2 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleSupportedCoefficientReduction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperSupportCompactMaps | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | F3 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarPresentationCokernel | R5 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | C1 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportComparisonBoundary | H7 | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportLongExact | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.AlgebraicGeometry.SupportSiteComparison | Q5 | Unchanged public API; no adaptation. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Compactification.NagataDensityNormalizationSheaves | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.FieldTheory.CondensedSubfieldBasis | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification | S6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.AdicHeartPullbackFibres | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.AdicPullbackPresentationTransport | M2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.AdicSmoothBaseChange | Y3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.AffineLineInvariance | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.AmbTateRootProjectionReduction | G3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.AmbientCompleteCoefficientCategories | B7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.AmbientCompleteRawSystem | H8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.AutomorphismCompletionUnitComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ClosedSupportBoundedContinuity | U2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ClosedSupportedCupVanishing | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CoefficientChangeDualizing | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CoefficientProjectionSquare | C4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CoefficientPushFilteredLegs | U2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CohomologyTorInterval | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CommonStageLisse | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CommonStageLocallyFree | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CommonStageWeilLinearDual | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportCompatibility | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompactProductProperSupportLaws | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompactProductRealizationCoreLaws | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompactProductRealizationLaws | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompactProductTwistLaws | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompleteCompactSupportProetale | A5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompleteProetale | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | B9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedCoefficientPresentationTransport | M3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | J4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedExchangeCoherence | S9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedLineComplete | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedLineDerived | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedOpenExchangeTransport | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedOperationTowerSubstitution | P3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedPullbackReduction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedPullbackTensorComparison | C5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedScalarChainShift | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedScalarShift | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletedTensorScalarLinearity | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CompletionTriangleComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | A3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedCompactSupportProjection | T2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | S2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | C6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ConstantDerivedLimitResolutionUnit | U5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ConstantWeilStructure | H9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ConstructiblePullbackTExact | C8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ConstructibleTruncations | C9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.CtfHomCoefficientComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.DegreeZeroDerivedMapGluing | J5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | R9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedCompleteOnSlices | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedExchangeExactNormalization | M4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedFiniteQuotientCoherence | W4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedNakayama | D5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorHom | K3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.DerivedPullbackTensorIso | J6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.DirectImageHomEvaluationSquare | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.DlLocallyConstructibleAdicHeart | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ECoefficientSmoothBaseChange | A6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | D7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.EtaleIntegralLineDerivedComplete | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.EtaleIsoDescent | R5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.EtaleLocallyClosedShriek | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.EtaleSitePerfectConstructibleHom | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ExplicitExceptionalPreservation | J7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FieldStageOrdinaryRealization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FieldTorAmplitude | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FilteredCoefficientTensorBounds | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | D9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientModelComparison | R8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientPoint | E5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientReductionFlatModel | E6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | J8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | E7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | E8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | G4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | F4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | Q2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | E2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingCompactification | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingNaturality | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteEncodingTensorTor | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEncoding | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteExtensionReductionConeBound | E9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | B5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteForwardProductSymmetry | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | V8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteProjectionActionLaws | J9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteProperBaseChange | U4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FinitePullbackTensorComparison | K5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FiniteTateSiteDescent | F5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FourierAdicArtinSchreier | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FourierTraceFunctions | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.FrobeniusCoefficientReductionMap | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | J2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.GeometricStalkPerfect | H3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IdentificationFibreAdjunction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralAmbientOperationModels | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralCoherenceTower | S3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralComparisonRealizationModels | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralComparisonSequenceSystems | W4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralCtfTriangulated | F6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralDerivedCoefficientData | D4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralHomAugmentedTowerComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralHomModelsExist | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralHomReduction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralHomReductionComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralHomReductionTowerComponents | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralHomRoosTransport | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralInverseImageComparisonComposition | K6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralLineReductionRestriction | Z5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralLineTensorComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralLineTensorComparisonDefinitions | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralLineTensorComparisonIso | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralLineTensorComparisonRepresentative | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralPointTransportTowerRealization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralPullbackComparisonRealization | F7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralPullbackCompletedComparison | A7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralPullbackReductionCounit | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralPullbackResolutionMatching | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralSystemPullbackLiftAssociativity | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralSystemReductionFullyFaithful | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralTensorReductionTowerComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralTensorTransitionCompatibility | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralTowerInverseImageUnit | Z9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntegralTowerLimitComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.InternalAdjunctionPairingChange | F8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.InternalHomDualTorAmplitude | Q4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwists | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IntrinsicQbarCategory | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.InverseImagePullbackComparisonDerived | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.IsomorphismComparisonScalarExtension | K7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.IsomorphismDerivedPullback | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusTrace | A8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.LocalModelTorBoundDescent | H4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.LocalWeilModelTraceIndependence | K8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.LocalizedTensorBraidingNaturality | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ModuleDerivedCompositorCoherence | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.NormalizedRationalEvaluationNaturality | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.OrderedExchangeCoefficientComparison | K9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | S4 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PbcCoefficientTwists | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PbcCohomologySheaves | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PbcConstructibleReductionPullback | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PbcDescentFunctors | A9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PbcIntrinsicTowerComplete | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PbcQbarCompletedPullback | M2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PbcQbarStandardCohomology | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PbcSupportCondition | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointDerivedHomEvaluation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointDerivedHomModels | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointExtensionKFlat | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensor | Q6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorBasic | Q9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorFiniteModels | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorModels | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorQbar | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorRational | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointFibreDerivedTensorScalar | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointFibreEquivalence | B5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointHomComplexAdjunction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointSectionsReconstruction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointSectionsScalarExtension | G3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointSheafHomMaps | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PointTensorHomEvaluation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PrincipalReductionConeCalculus | S6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ProjectionFormulaCoefficientCoherence | M6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PurAdicScalarExtensionTorBound | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus | M7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PurTwistSheafLocallyFree | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PurityFiniteKummerLevel | M8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PurityFiniteOpenIntervalDescent | M5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.PurityGeneralAdmissibility | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.PurityRankOneLocalCalculation | M9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | B6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.QbarIdempotentComplete | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.RealWeilSheaves | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.RealizationScalarFunctor | P3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | P5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.RoosIntrinsicCompletenessEquivalence | F7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SbcCompletedOperations | B2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.ScalarCompletionAssociator | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ScalarExtensionExactIntrinsic | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ScalarExtensionTensorUnit | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.ScalarExtensionTowerCoherence | P6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SectionDerivedRealization | T1 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfCbcCompactSupportCompositionLimit | F9 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfCbcExtensionZeroCompletion | G5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfCommonStageWeilCohomology | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfConstructibleCanonicalCompleteness | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfConstructibleHeart | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfExchanges | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfImmersionCompletedPullbackComparison | V2 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfIntegralConstructibleLinear | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfIntegralConstructibleTriangulated | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | K3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfRationalBoundedConeTorsion | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfRationalizationKaroubi | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfScalarExtensionComposition | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SfWeilSheafComplex | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SignedLineTensorEquivalence | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SignedTwistReductionComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SiteComparisonEdgeSection | Q7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SpecifiedPullbackComparisonAlpha | Q8 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedClassGeometry | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedClassSiteComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedCupFunctoriality | G6 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedExteriorClassArrows | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedExteriorShift | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | P7 | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedTwistDegreeZeroProduct | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedTwistMultiplication | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.SupportedTwistPullback | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | P5 | Unchanged public API; no adaptation. |
| Sheaf.Paper.TwoTermReductionCohomology | E3 | Unchanged public API; no adaptation. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.WeilComplexQbarIdempotentComplete | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.WeilComplexTraceFunction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Paper.WeilIndSheafCategory | G7 | Unchanged public API; no adaptation. |
| Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SecSmoothPurity.WeilTwistRationalization | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.BoundaryDualityInput | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | G8 | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.FiniteCoverCTFLocality | H2 | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransport | G9 | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.FrobeniusPointTransportNatural | H5 | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.IntegralOpenReductionComparison | V3 | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | E4 | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.OpenSemilinearTensorModel | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | B2 | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData | X2 | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.ScalarSixPullback | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.SchemeFrobenius | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.SixFunctors.SchemeGaloisComparison | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Targets.VectorBundlePurity | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.Topology.ProfiniteSectionsFiniteQuotient | U3 | Unchanged public API; no adaptation. |
| Sheaf.Topology.TopologicalModuleCondensation | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.TraceFormula.AlgebraicShriekCalculus | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.TraceFormula.AlgebraicShriekRelativePerfect | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.TraceFormula.CompactSupportSystemEvaluationDiagram | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization | P8 | Unchanged public API; no adaptation. |
| Sheaf.TraceFormula.PointTransportComposition | H6 | Unchanged public API; no adaptation. |
| Sheaf.TraceFormula.PolynomialDiagonalRhomReduction | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.TraceFormula.UpperShriekBoundedCoherent | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.WeilSheaf.AdicFiniteCoefficientBound | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Unchanged public API; no adaptation. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Unchanged public API; no adaptation. |
| TargetsCheck | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Basic | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Frobenius | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Stalk | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.TraceFormula.WeilTrace | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.Homology | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Unchanged public API; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Unchanged public API; no adaptation. |

## Status

landed 20261021T120414-L-3885937 2026-10-21 (merge of deliver/H4/Sheaf.Algebra.Homology.ScalarHomTensorCoherence)
