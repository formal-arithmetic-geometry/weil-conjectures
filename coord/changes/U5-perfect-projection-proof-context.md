# PerfectProjectionFormula proof infrastructure and local context

## Reason

Fold completed-coefficient, tensor and localization constructions during proof
conversion, and reuse three existing site-infrastructure proofs. All local
attributes and instance priorities are confined to this module. The restricted-unit argument is proved over arbitrary coefficient
sheaves and specialized only at the end. The resolution-existence proof enables
let-to-have cleanup locally. The ordinary restricted-unit proof reuses the
existing mate and adjunct equations through a private import-all; the quotient
compositor reuses a proved generic derived degree-zero compositor helper. The three new
public theorems are fully proved by existing instances, and are registered only
locally. They change no mathematical data. No private declaration occurs in a
public definition. The public signed-normalization import exposes the existing model constructors;
the definition records explain their identical mathematical values.

## Old

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] mixed proEtaleMixedTensor
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
attribute [local irreducible] SheafOfModules.monoidalCategory
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] CategoryTheory.tensorAdjunctionTotal
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleRingDerivedPullbackFactors
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local irreducible] proEtaleProjectionFormulaMate proEtaleAmbientRingedExchange
  proEtaleCanonicalTensorComparison
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

## New

```lean
public import Sheaf.Paper.SignedProjectionResolutionNormalization
set_option Elab.async true
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 30000]
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
attribute [local instance 2000] CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape
  CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
attribute [local instance 3000] completedCommRingWeakSheafify completedRingWeakSheafify
  completedCommRingLimits
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
attribute [local irreducible] coefficients SheafOfModules.monoidalClosed_kfg
  SheafOfModules.monoidalCategory
  CategoryTheory.tensorAdjunctionTotalInverse CategoryTheory.tensorAdjunctionTotal
set_option linter.flexible false in
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option cleanup.letToHave true in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
attribute [local irreducible] proEtaleOrdinaryTensorPullback
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleDirectImage
  proEtaleRingModuleAdjunction proEtaleRingDerivedPullbackFactors
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option cleanup.letToHave true in
set_option linter.flexible false in
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingCompositeCoefficients proEtaleRingDerivedPullbackFactors
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
set_option cleanup.letToHave true in
set_option linter.flexible false in
set_option cleanup.letToHave true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
set_option linter.flexible false in
attribute [local irreducible] proEtaleProjectionFormulaMate proEtaleAmbientRingedExchange
  proEtaleCanonicalTensorComparison
set_option linter.flexible false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option cleanup.letToHave true in
set_option linter.flexible false in
```

The added proved theorems are `completedCommRingWeakSheafify`,
`completedRingWeakSheafify` and `completedCommRingLimits` in namespace
`AlgebraicGeometry.Scheme.PerfectProjection`. Their statements are existing
infrastructure propositions; each proof is `inferInstance` before its local
registration. The original node lists all three. The signed map reuse is separately documented in the total-inverse record.
Retained public theorem signatures are preserved; unused duplicate interfaces are
listed in the pruning record. The private `strictPerfect_mem` is completely proved.

## Users

The following complete import closure is obtained by
`tools/downstream.py Sheaf.Paper.PerfectProjectionFormula --names`.
Local attributes and local instances are not exported. Existing declarations
keep their meanings and signatures; consumers using changed definition names
are examined separately in the ring, mixed and total-inverse change records.
These indirect importers require no source adaptation. Claim holders are from
the current local snapshot; unclaimed means no matching active claim was found.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CoefficientMateDiagonalGraph | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ComponentPullbackUnboundedEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientPresentationIdentification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedComponentInverseImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedComponentPullbackCompatibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedCoverRestrictionConservative | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | P8 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedLisseEvaluationModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedLisseProEtaleLocality | Q5 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedLocalizationExactCohomology | P9 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedOpenAdjunctionLocalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedProfiniteScalarCompatibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ConstructibleCoconeAmbientRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ContractibleEvaluationAdjunction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.EllAdicProperHeartUniformBound | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingCoproducts | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.EtaleChartComparisonIsos | J4 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FieldActionCoefficientTransportData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FieldActionDerivedSectionTransport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FieldActionScalarTransportData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FieldActionTransportData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FiniteCoefficientEtaleProjectionFormula | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FiniteConstantLocalModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfOrigin | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FiniteDiscreteCtfRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.FrobeniusContractionScalarPasting | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.GenericComponentCoefficientComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.GenericFiberComponentsSection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.IdentityOpenModuleSections | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.IntegralDerivedExtensionComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | W6 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport | X7 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.KInjectiveDirectImageOpenWordModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.LocalModelCohomologyDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ModuleDirectImageOpenPasting | V1 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.NativeAdicAffineOpenZeroStratification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.OpenExtensionRHomContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ProEtale.CondensedRing.BoundedConstructibleOpenImmersionLowerShriekUpperStarAdjunctionAlias | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | J6 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ProperOpenComplementSquare | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | W3 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.QcqsClosedPullbackFiniteModelCompletion | V4 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryFunctor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing | T3 | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.RelativeSingleTensorCohomology | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ScalarMatrixInverseImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.ScalarPresentationCokernel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.SfEtaleExchanges | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedActionModule | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedActionTensor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedBarScalarResolutionComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedBarTotalAugmentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedBarTotalNaturality | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedCentralActionDerivedVanishing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedDerivedCup | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedDerivedInflationArrows | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedDerivedInvariantBar | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedDerivedInvariants | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedEquivariantBarData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedGroupAlgebraExactForgetful | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedHomogeneousFunctionsInjective | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedInjectiveBarRows | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedInternalBarResolution | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedNormalInvariantData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedNormalSubgroupComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedProductActionInflation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedProductBarComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedRestrictionMateNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedScalarTensor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedSplitCosetInduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedTensorInductionAdjunction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CondensedUnipotentClass | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.ContinuousScalarRing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.CyclicTotalTriangulated | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.DiscreteLatticeCupExterior | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.DiscreteLatticeKoszulResolution | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.EquivariantResolutionBarNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.InternalBarFiniteIndexTransfer | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.InternalBarOrderedCup | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.InternalBarRoofAdjunction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.InternalFunctionVertexPrism | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.InternalHomogeneousCochainCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.InternalInflationGradedCup | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.LatticeAlgebraDerivedCup | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.LatticeDerivedInvariantsTensor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.LatticeRestrictionCupComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.NormAlgclBarAugmentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.NormedScalarProfiniteHomAcyclic | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.OpenNormalActionInjectiveModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.PointedFreeDeletionContraction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.PolynomialDerivedBarComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.PolynomialTranslationAcyclic | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.PrimeToEllCondensedAcyclicity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.ProfiniteActionCoherentPresentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.ProfiniteActionParameters | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.ProfiniteInvariantsFilteredContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.RelativeBarData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.RelativeCoefficientComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.RelativeCyclicRestrictionModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.RelativeCyclicTotal | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.RelativeDerivedInvariants | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.RelativeInvariantForgetting | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.RelativeLatticeBridge | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.RelativeTrivialCyclicMap | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Compactification.NagataDensityNormalizationSheaves | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.DeligneLaumon.Reduction.FinitePushforwardPunctual | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.FieldTheory.CondensedSubfieldBasis | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.FourierTransform.FourierDeligneTransform | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.NumberTheory.Padics.BaseCoefficientCondensedIdentification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.NumberTheory.Padics.FiniteIntegralCondensedResolution | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicFibreComparisonCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicFibreComparisonData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicHeartIntrinsicFibres | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicLocalCharacteristicFactor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicLocalFrobeniusModelConjugacy | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicNormalizedFibreData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicNormalizedFibreExactness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicPunctualWeights | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicPurityFiniteTensor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicPuritySourceFiniteness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicPuritySourceReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicPurityTwistReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdicStratifiedPullbackInterface | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AdmissibleScalarRealizationExact | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AffineDiagonalTensorCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AffineProperSquareStratifiedModule | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AffineTranslationTrace | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.AmbientQcqsExchangeCanonicalShifts | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.BoundaryOrdinaryImages | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.BoundedConstructibleBaseChange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.BoundedConstructiblePushforwardRestriction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.BoundedFiniteModelGeneration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.BoundedFlatTensorContinuity | B2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CanonicalPointScalarComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | B9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CleanOpenUnitParametrizedExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClopenCanonicalFiniteEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClopenCanonicalRestrictionEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClopenExceptionalScalarDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClopenSystemFiniteRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClopenSystemIntegralRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClopenSystemRestrictionEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedLiftedTestIsomorphismCriterion | T9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedSupportBoundedContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTestChainMateRestriction | F4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTestDerivedExchangeModel | A2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTestKInjectiveSectionModels | M8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTestLocalizedModelCoherence | E2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTestScalarComparisonMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTestScalarModelCoherence | K2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTestScalarModelDiagrams | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTestUnitEvaluation | Z6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ClosedTorsionRigiditySerreTransfer | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientFiniteDescentHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeart | C6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartCurveComplement | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartCurveLisseDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartFiltration | D2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartLocallyClosedExtension | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientHeartTriangulated | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientProjectionSquare | N1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientPushFilteredLegs | C5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CoefficientScalarTensorRealization | D7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CohomologyTorInterval | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CommonStageCurveWeilMiddleExtension | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CommonStageFourierTransform | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CommonStageWeilFourierTransform | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompactAdicContinuousIdentification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompactFiberStalk | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompleteCompactSupportProetale | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompleteGroupTorsorMonodromy | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompleteIntegralResidueFunctor | T2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompleteResidueLineInverse | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletedCompactSupportExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletedConstructiblePreservation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletedConstructibleReductionControl | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletedFrameGenericComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletedMapReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletedOpenFiniteTransposeCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletedReductionSquare | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompletionTriangleComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ComponentDerivedPullbackSquare | C1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ComponentLiftLisseSectionComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CompositeModuleOplaxMate | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedCompactSupportProjection | U8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedERealization | D3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedLocalizationHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedOpenExceptionalProjectionFormula | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedOpenSquareScalarComparison | U9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedPointCoefficients | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedPointDiscreteConstantComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedPointModuleComparison | V1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedScalarFinitePresentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedTateRealization | D5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CondensedZlReduction | W3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstantModelStratificationTransport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstantSquareZeroTorExample | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstantToContinuousScalarFlat | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleCompleteBaseChange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleMateCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleNormedGeometricFibres | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ConstructibleProjectiveChartRefinement | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousAlgClFiniteStageDevissage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousAlgclScalarConstructibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousCoefficientFreeRank | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLissePullbackSystem | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousLisseStratumDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousModuleSectionModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousQbarConstructibleGenerators | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousQbarLisseHeartClosure | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousQbarNormalizedSheafFiltration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousRepresentationCondensation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ContinuousScalarDerivedEncoding | V8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.CurveWeilMiddleExtension | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DenseLatticeDerivedInvariants | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DenseOpenPiOneSurjective | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | D4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.DerivedExchangeExactNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DerivedNakayama | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DerivedNakayamaResolution | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DerivedOpenSquareRestriction | C6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.DerivedWeilOperations | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DeterminantalWeightCoefficientField | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalAffineTraceCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalAffineTraceSiteComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalTowerCoefficients | U4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalTowerLimit | E6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalTowerSystem | E1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalTowerTrace | E7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EmbeddedLatticeCoefficientComparison | V9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.EquivariantAdicFibreCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EquivariantAdicFibreData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EquivariantAdicFibreNaturalityData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EquivariantAdicFibreRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EquivariantAdicFibreRealizationData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EtaleBrownProjectionRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EtaleSystemBrownConstruction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EtaleSystemCoefficientProjection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EtaleSystemCofinalMate | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EtaleSystemEvaluationBound | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EtaleSystemProjectionData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EtaleSystemQuotientNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EtaleSystemScalarMateCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.EvenTensorPositivity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FdCompletedCompositorNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FieldActionToposCoefficients | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FieldLisseStratifiedHeartSupport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FieldSeparableCechCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FieldWeilShriekShiftData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteClosedShriek | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteCoefficientDerivedExchangeIdentification | D8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteCoefficientModelComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteComparisonLocalizing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteComparisonPresentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteConstantModelResolution | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteConstantModelStrataGeneration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteConstantModelsCommonStratification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteConstructibleModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteEncodingCompactification | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteEncodingConstructibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteEncodingNaturality | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteEncodingPullbackFixed | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteEncodingTensorTor | U3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEncoding | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteDiscreteScalarConstantModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteExtensionCompactSupportBaseChange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteExtensionProperBaseChange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteFieldClosedSupport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteFieldHomEtaleWitness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteFreeDualChainComparison | E5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteImageOpenKernelInflation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteModelSheafQuotientConstructible | X7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteModelStratumFiltration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FinitePrincipalSupportUnitAssembly | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteProperBaseChange | E8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteReductionChartCalculus | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteReductionComparisons | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteReductionRootCharts | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteRingSectionDeformation | F2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteScalarLocalModelComplete | X9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | G1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteStrataCompletionDetection | Y6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteTateBalancedScalarPullback | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteTateScalarSourceNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteTensorComparisonEquations | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteWindow | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FlatCoefficientSquareNormalization | R9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.FlatCondensedScalarRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FormalClosedSupportDerived | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FormalClosedSupportSheaves | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FreeParameterDegreeZeroData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FreeParameterEvaluationCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FreeParameterEvaluationData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FreeParameterMatrixCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FreeParameterRelativeMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FreeParameterScalarMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.FrobeniusCompactSupportExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.GenericLisseScalarComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.GeometricFiberFiniteExtension | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.GeometricFiberQbar | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | E8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | F5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IndUnipotentProcyclicDifference | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IndUnipotentSystem | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralAdicHomCompleteness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralAdicHomResidueOrigin | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralAdicInputNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralAugmentedQuotientTowers | Y7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralBoundedStratumBaseChange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralCoefficientExtComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralCoefficientModelRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralCoefficientSquareNormalization | Y8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralCompactSupportUniformRestriction | T4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstantModelHeart | Z8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstantModelLocalResolution | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstructibleHeart | F5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralCriterionReductions | C9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralDerivedCoefficientData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralExtensionByZero | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralFibreSectionSpecialization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | J7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralGeneralLfpSequentialContinuity | W4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralHeartLocalDualityDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralHeartLocalModel | Z9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralHenselianLisseSectionRigidity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralLisseClosedBaseChange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralLocalizationHomColimit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralModelSurjectiveClosedReflection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralModels | J8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralModelsOperations | V1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralOpenExtensionReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | F6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | J9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | K5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | K9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralQuotientPullbackFaceModel | H1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralQuotientResolutionNormalization | H2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | H3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralResidueClassTriangleClosure | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralRoosDerivedPullbackUnit | A3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralScalarConstructibleImage | E2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralSectionLocalModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralStratumHomFormula | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTensorPullback | H4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTensorShriek | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalDerivedClosedLocalization | F7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalDirectImageLaxRealization | H8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalHomDualTorAmplitude | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalScalarMateProjection | J3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalScalarMateTransitivity | J4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalScalarProjectionMate | K1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalScalarPullbackNormalization | K2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalSectionHomComparisonData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalSectionHomContinuityComparison | K3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.InternalSectionScalarHomTransportData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntrinsicConstructibleFibreExactness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.IntrinsicLocalLatticeComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KFlatDerivedAdjunctionTransportShifts | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerBarResolution | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerNormalizedComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerPartialNerveChart | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerPartialNerveCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerPartialNerveMorphism | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerPartialNerveScalarMorphism | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerRefinement | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerResolutionColumns | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerScalarRestriction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerStratumScalarMaps | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerStratumScalarMateDetection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerSuccessiveDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.KummerTermMate | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseDenseOpenRecovery | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseEConstructibleIntegralLattice | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseExtensionInertia | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseIntegralCompletedRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseLatticeReducedOpen | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseOpenUnitTestDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LocalModelTorBoundDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LocalizationScalarUnit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LocallyClosedScalarPasting | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LocallyConstantPerfectComplex | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LocallyFiniteAdicConstructibleRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.LocallyFiniteCoefficientRingRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.MixedWeightsStability | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ModuleDerivedFunctorCompositorShifts | P2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ModuleDerivedFunctorShifts | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ModuleRingedToposDerivedComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ModuleSectionDerivedComparisonSquare | M2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.NativeAdicCompactSupportSums | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NativeIntegralTateTowerLimit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NativeWeilClosedForgetful | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | M3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.NoetherianStratifiedModelProductEmbedding | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NonaffineClosedTestExchangeIdentification | E5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormAlgclCohomologyTopologyComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormalGenericLisseCocycle | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormalizedCoefficientFamilies | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormalizedHeartRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormalizedInternalSupportScalars | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormalizedLatticeFiniteFree | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.NormedCoefficientRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.OpenExtensionConstantModelConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.OpenExtensionConstructibleFiniteTor | W4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.OpenFiltrationSuccessor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.OpenInternalKFlatMateNormalization | F9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.OpenSquareClosedUnitTriangle | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.OpenSquareSupportScalarCounit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ParameterRootBoundaryData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ParameterRootIntegralNilFibre | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PerAdicNormalizedFibreComparisons | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PerfectProjectionFormula | U5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.PointPullbackDerivedHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PointRealizationCoefficientComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PrimeToEllDerivedInvariantsReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PrincipalReductionConeCalculus | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PrincipalReductionDerivedNormalization | Q8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProEtaleScalarLocalModelRepresentatives | U2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | G7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProEtaleTateTwists | A9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProfiniteConstantDerivedFunctions | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProfiniteDerivedEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProfiniteDerivedFunctionsFilteredColimit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProfiniteFreeSliceDerivedHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProjectionSectionNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProperHeartBoundLattice | G8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProperHeartBoundReduction | H5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProperHeartBoundTorsion | A2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | Y8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProperUnboundedWindowBounded | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ProperWContractibleClosedFibreRigidity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PunctualSpectrumExactFibre | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurityConventions | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurityDiagonalDualizingObject | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | H6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.QbarCompactSupportBaseChange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.QbarCurveOrdinaryImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.QbarProperBaseChange | G1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcOpenExtensionConstantModelFiniteTor | X3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcqsConstructibleIntegralLatticeTree | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | H8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcqsIntegralScalarExtensionCTF | H9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcqsLatticeTreeReconstruction | B4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcqsLisseStratifiedIntegralLattices | A3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | N1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcqsProperSerreHeartBound | R1 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | Y2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QlbarBoundedTensorColimit | N2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QlbarDirectImageComparison | W2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | P7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QlbarTailFiniteFreeAlgebraPresentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.QuotientPullbackCompositorNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.QuotientPullbackTensorCoherence | N3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.QuotientSectionTensorNormalization | N4 | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalCompactSupportCoefficientCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalRealizationPullbackComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalRealizationScalarCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalStratumIntegralModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealSheafSections | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealWeights | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationAdjointComparisons | D6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationCoefficientSquare | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationCompletedImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationCompletedPull | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationCompletedPullData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationContinuousDirectImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationLocalizedPush | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationPullOrdinarySystem | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationPullRationalDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationRestrictionNormalizations | Q7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationScalarFunctor | J5 | Same retained statements; local context is not exported. |
| Sheaf.Paper.RealizationScalarPushMate | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RestrictedCoefficientMateProjection | S7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RootCoordinateSupportedVanishing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RootTowerCoordinateFace | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.RootTowerPunctureInvariance | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ScalarChangeDirectImageUnit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ScalarGeometricExchangeRectangle | J6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ScalarModelImmersionExtension | P9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.ScalarModelRestrictionCriterion | B9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionDerivedOpenAdjunctionNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionDerivedPushpullNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionDerivedRealization | J8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionDerivedRepresentativeSquare | Z6 | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionDerivedTensorData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionDerivedTensorNormalization | Y7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionKFlatTensorComparison | K7 | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionModuleOperationsData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionOplaxTotalComparison | E3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionOrdinaryOplaxNormalization | J9 | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionTotalOplaxComparisonData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SectionwiseOpenLisseHomDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SfExchanges | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SfLocalizationAllStages | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SmoothPurityMap | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SmoothTrace | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SpectralFiniteEtaleTraceLattice | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.StratifiedConstantModelProductBound | C8 | Same retained statements; local context is not exported. |
| Sheaf.Paper.StratifiedDualizableBounded | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.StratifiedDualizableHomContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.StratifiedLattice | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.StratifiedLatticeRank | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.StratifiedLatticeScheme | C3 | Same retained statements; local context is not exported. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.StrictCompletionRestrictionComparison | F2 | Same retained statements; local context is not exported. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TAdmissibleCoefficientModels | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TameBoundaryScalarComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TameInertiaContinuousKoszul | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TameInertiaScalarMate | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TameIntegralReductionFamily | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TorsionAcyclicNormCoefficientTest | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassChern | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TransverseTameOpenShriekExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TrivialLadicDerivedExterior | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.TwoTermReductionCohomology | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.VectorBundleDiagonalOrientation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.VectorTraceScalarDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WContractibleComponentDerivedHom | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WStrictLisseComponentCohomology | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WeilFourierTransform | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WeilGenericLissity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WeilKernelHenselianInertia | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WeilMixedUpperBounds | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WeilShriekShiftCompatibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WfTateTwist | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ZlFrameworkOpenExchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ZlFrameworkPbcOpenComparisonData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ZlOpenDiagramComparisonTransport | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Paper.ZlWeilShriekCoefficientLongExact | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.PoincareDuality.OpenModuleBalancedProjection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.PoincareDuality.OpenModuleKFlatProjectionModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.RepresentationTheory.ProcyclicScalarCochainEvaluation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.RepresentationTheory.ProfiniteAlgclDerivedInvariantsComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | Q1 | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.BrownHypothesesAmbient | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.CoefficientDualizingClosedDescent | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.FiniteCompactProetale | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.FiniteCtfInternalEtaleRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.FiniteEtaleOpenUniformTorImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.FiniteFreeImageComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.FiniteOpenDirectImageCtf | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.IntTensorProjection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.IntegralOperationShiftData | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenScalarAdjunctionCounit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenScalarConjugateNormalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenStarShriekScalarMateSquare | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | T5 | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares | M5 | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ScalarSixHeartLatticeExtension | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ScalarSixLisseTowerComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.ScalarSixPullback | T7 | Same retained statements; local context is not exported. |
| Sheaf.SixFunctors.SupportedWeilMateLift | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Q3 | Same retained statements; local context is not exported. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Topology.ContinuousAbelianProfiniteSheaf | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Topology.ContinuousModulePresheafCoordinates | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Topology.ProfiniteCondensedRing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Topology.ProfiniteSectionsFiniteQuotient | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.Topology.TopologicalModuleCondensation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.TraceFormula.CondensedStalkFrobeniusOrbitTrace | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.TraceFormula.WeilUnit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.UpstreamExtra.WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.UpstreamExtra.WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.WeilSheaf.DerivedHomSingleResolution | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.WeilSheaf.NativeBasicComparisons | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.WeilSheaf.NativeCompactificationModelComparison | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.WeilSheaf.NativeCompatibleTowerCalculation | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.WeilSheaf.NativeOpenProperInterchange | unclaimed | Same retained statements; local context is not exported. |
| Sheaf.WeilSheaf.ProperSheafFiniteness | unclaimed | Same retained statements; local context is not exported. |
| TargetsCheck | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.ArtinSchreierDual | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Constituent | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.LaurentPoints | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.LinearCharacters | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Punctual | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualSupport | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.RamifiedAtInfinity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.AdicReconstruction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryGenericRep | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodConstruction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryNeighbourhoodExistence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LisseWeilSheafTensor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentationTensor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSections | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationFunctor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationTensor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicFrobenius | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.AdicSystem | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundedConstructibleUpperShriek | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeExchange | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeStalk | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImageReduction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralConstructible | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.Perfect.PointPerfectness | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberAlgClosed | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberIntegral | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.PointFiberRational | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalOperations | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicAbIdentification | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.AdicConstantSheafLeg | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedLowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.DerivedForget | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.FiniteAdicHFinite | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.GlobalSectionSMulUpperStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafBasis | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafStageMap | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeApproximation | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIdentification | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeIntegrality | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeKernel | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeScalarLinear | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeSemilinear | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.IntegralLatticeTensorBijective | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverEquivalence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyLift | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyPullback | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerShriekFiniteness | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantBounded | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFiniteness | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarConstantFinitenessStratum | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissage | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarDevissageRegular | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisse | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarStratumLisseComponents | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarScalar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.SmoothProperLatticeAdic | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.Adic.UpperShriek | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | D4 | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarEllAdic | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.Statement | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilObject.BoundedConstructible.Homology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.AlgClosedCoefficientCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierFunctions | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierInertia | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierIsotypic | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierMul | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierMulGeometric | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierNeg | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierPlane | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierPullback | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrivialization | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.BaseChangeField.Cohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.BaseChangeField.Comparison | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.BoundaryStalk | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.BoundaryStalkFrobenius | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.BoundaryStalkGaloisInvariants | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.BoundaryStalkSpecialization | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.BoundaryStrictHenselization | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ClosedLowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Cohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstant | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstantExt | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyAdicConstantLattice | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyExact | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyGeometricConjugacy | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyGeometricEquivalence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyNonneg | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyProEtale | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyResolution | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologySequence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyShift | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CompactSupportAdicConstant | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ComplexWeights | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ConstantTwistWeight | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Defs | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.DenseOpen | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.DerivedHom | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.DirectImageStalk | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ExtensionByZero | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ExtensionByZeroAdjunction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ExtensionByZeroDerived | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FieldCoefficientCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FieldCoefficientForget | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FieldCoefficientFrobeniusTwist | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FiniteEtale | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FiniteLeray | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FiniteLowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FinitePointCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Fourier | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierTateTwist | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FourierTraceAux | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.FrobeniusTwist | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.GlobalSectionsUpperStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.IhomCurry | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.IhomLisse.CompWeil | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.IhomLisse.UpperStarDual | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.IntegralCoefficientCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Isotypic | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.IsotypicPullback | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Karoubian | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.KaroubianPointer | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LSeries | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LisseExtension | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Localization | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerShriek | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerShriekIndependence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerStarComp | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerStarId | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerStarPairing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.LowerStarTriangulated | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.MiddleExtension | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.OpenImmersion | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Operations | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.PoincareDuality | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.ExtensionByZero | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerShriek | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ProperBaseChange | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ProperBaseChangeFunctor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ProperCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Realizable | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.ShiftedSheaf | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.SplitTorsor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkInternalHom | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkRationalPoint | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkStrictlyHenselian | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkTateTwist | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkTensor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.StalkTensorTrace | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TateTwist | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.Tensor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TensorHomAdjunction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TensorObjPairing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TensorPower | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TorsorPairing | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TraceCupAdicConstant | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TraceFunction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.TraceSeries | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.UpperStarLowerStar | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunctionWeil | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Same retained statements; local context is not exported. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Same retained statements; local context is not exported. |

## Status

landed 20261024T191427-L-349376 2026-10-24 (merge of deliver/U5/Sheaf.Paper.PerfectProjectionFormula)
