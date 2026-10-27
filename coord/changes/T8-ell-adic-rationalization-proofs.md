# AlgebraicGeometry.ProEtale.isLocalization_boundedConstructibleExtendScalars

## Reason

Close both holes in the assigned source module from its existing DAG dependencies.
Local reducibility commands prevent unfolding large coefficient-pullback and derived
functors during proof elaboration. All six added imports are private proof imports.
The archive import uses `import all` to access its existing proved private helpers.
There are no new declarations, changed signatures, public imports, global attributes,
or non-theorem data changes. No target meaning changes or target review is reopened.

## Old

The signatures, verbatim, with bodies `sorry`:

```lean
lemma boundedConstructible_derivedExtendScalars_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)
      ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj K)

instance isLocalization_boundedConstructibleExtendScalars :
    (boundedConstructibleExtendScalars X ℓ E).IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ))
        (BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
```

## New

The same signatures, with complete proofs:

```lean
lemma boundedConstructible_derivedExtendScalars_obj
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E.1) X)
      ((Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj K)

instance isLocalization_boundedConstructibleExtendScalars :
    (boundedConstructibleExtendScalars X ℓ E).IsLocalization
      (Rationalization.W (Submonoid.powers (ℓ : ℤ))
        (BoundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X)))
```

Preservation specializes exact continuous integral scalar extension and the generic
bounded-constructibility theorem. Localization transports triangulation along the
canonical comparison with exact termwise extension and supplies integral models,
denominator clearing, scalar invertibility and scalar equality detection to the
existing proved full-subcategory localization helper.

The only added commands outside theorem bodies are:

```lean
attribute [local irreducible] upperStarFromPoint Mod.extendScalars
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
```

These attributes expire at the end of the existing namespace. They change no exported
attribute, definition, structure or statement. Every original definition body, original
instance other than the assigned holed localization instance, declaration signature,
visibility and public import is preserved verbatim.

## Users

`tools/downstream.py` found 295 downstream modules. All keep exactly the same
public interface, since the changes comprise proofs, private imports and local proof
elaboration attributes. No adaptation is necessary. The declaration-name scan for the
localization instance found only its own declaration, with implicit downstream uses
retaining the identical instance type. Current local claim records supply the holders
below; the dispatcher's assignment supplies this item's holder.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | T8 (dispatcher assignment) | Existing interface and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteClassicalLocalizing | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralDerivedExtensionComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleCompletedCoefficients | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryFunctor | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.RegularImmersionSmoothStructure | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.AdicConstructibilityPredicateComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.AffineProperSquareStratifiedModule | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.AlgClTopologyMateHomBijection | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedSums | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.AmbientIndDerivedTriangulated | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficientTwists | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficients | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CartesianCoefficientsFiniteFree | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CartierClassAgreement | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ClosedSupportConstructible | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeart | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartFiltration | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartGeneration | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartLisseExtensionConstructible | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartLocallyClosedExtension | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CoefficientHeartSheafConeWitness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CondensedBoundedHomContinuity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CondensedOpenSquareScalarComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CondensedTateRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.CondensedZlReduction | Q4 | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleAlgClTopologyComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleCompactnessBounded | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleExtContinuity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleHomContinuityDevissage | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClFiniteStageDevissage | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenFiniteness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAlgClOpenScalarComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousModuleSectionModel | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ContinuousQbarNormalizedSheafFiltration | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DerivedDirectImageOpenCoherence | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DerivedGeometricStalk | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DerivedOpenSquareRestriction | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DetIndHeartIISums | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerSystem | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreCoordinates | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreData | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreNaturalityData | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.EquivariantAdicFibreRealizationData | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FdCompletedCompositorNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteLocalModelRHomContinuity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteModelSheafQuotientConstructible | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteModelTopologyComparisonMaps | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteModelTopologyDerivedHom | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteRingSectionDeformation | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothGammaNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteSpanModuleDerivedComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteStageSupportedGeneration | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteStrataCompletionDetection | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupport | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportII | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.FormalClosedSupportIILimits | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.GeometricCondensedFiniteScalarModel | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedAdjunctionNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IdentityOpenDerivedRestriction | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleExtensions | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IndConstructibleFilteredColimits | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IndHeartCanonicalPresentation | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IndHeartFullFaithfulness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IndHeartIIVanishing | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IndHeartKernelsCokernels | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAdicHomCompleteness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAdicHomResidueOrigin | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAdicInputNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAmbientCoefficientPresentation | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAmbientDirectImageEncoding | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralCoefficientModelRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralCoefficientSquareNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompactness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleReductionFibres | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomInversion | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpSequentialContinuity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndHeartRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralIndLowerTail | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralModels | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralPullbackStrictRoosNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientCoefficients | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientDirectImageComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientExchangeComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientProjectionMap | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientPullbackFaceModel | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientResolutionNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralQuotientSectionMateRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralRoosDerivedPullbackUnit | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralSectionLocalModels | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChange | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistBaseChangeDefinitions | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalar | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistDerivedScalarCanonical | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistScalarCoherence | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralTwistSchemeCompatibility | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralWindowCoproductComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.InternalHomDualConstructibleModels | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerAdditivity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerChartGeometryMaps | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerCoefficientModels | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerCoherentRoof | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerConstantNerveTerm | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerGeometricColumns | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerGlobalChart | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerInvariantScalarMap | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerLocalSource | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerNerveCoordinates | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerNerveGeometricMap | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerNerveTransport | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerNormalizedChart | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerParameterizedTerm | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveChart | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveCoordinates | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveMorphism | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveNaturality | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerPartialNerveScalarMorphism | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerRefinement | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerResolvedDescent | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerScalarInvariantSquare | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerStratumChart | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerStratumGeometry | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.KummerSuccessiveDescent | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.LatticeSubquotientFiltration | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.LatticeSupportedHomFiniteComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.LisseLatticePotentialKummerTameness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizedDirectImageComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.LocalizingClosureCtfEqualsBc | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.NativeDerivedWeilTensorConstructible | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.NativeIntegralTateTowerLimit | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.NoetherianEtaleSectionSpecialization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.NoetherianStratifiedModelProductEmbedding | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.NormAlgclOrderedFiniteModelFiltration | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.NormalizedInternalSupportScalars | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.NormalizedOpenRefinementCoherence | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.OpenSquareSupportScalarCounit | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.OrientationFiniteCoefficientTwists | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.OrientationFiniteReductionTwists | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.OrientationIntegralCoefficientTwists | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PadicIntegersInvertEll | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PartialKummerBoundaryUnitModel | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PointTateFiberCoefficientComparisons | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleScalarLocalModelRepresentatives | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwists | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ProEtaleTateTwistsOfUniverses | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ProperHeartBoundReduction | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ProperIntegralRationalScalarComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PurIntegralTwistLineInverseImage | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PurityConventions | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PurityExteriorProductFrame | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.PurityTwistCancellation | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QbarCohomologyFiniteLevelComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QbarTwistCommonStage | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QcOpenExtensionConstantModelFiniteTor | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QcqsConstructibleIntegralLatticeTree | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QcqsIntegralScalarExtensionCTF | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QcqsLatticeTreeReconstruction | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QlbarBoundedTensorColimit | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QlbarDirectImageComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QlbarInternalHomCoefficientComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QlbarTailFiniteFreeAlgebraPresentation | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QuotientPullbackTensorCoherence | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.QuotientSectionTensorNormalization | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RationalClosedSupportConstructible | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RationalOpenDirectImageConstructible | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RootBoundaryComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RootBoundaryScalarComparison | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RootTowerBoundaryAcyclicity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RootTowerInnerSupport | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.RootTowerLisseMorphismExtension | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.ScalarModelImmersionExtension | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientation | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationFiniteFamily | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityTowerP1Adjunction | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.StratifiedConstantModelProductBound | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.StratifiedLatticeScheme | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.StratifiedTorIntervalDevissage | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarData | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedCommonFieldScalarModels | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedExteriorClasses | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedFiniteStageTopologyDefect | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TameRootTowerExtension | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TameStratumKummerDescent | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TopologicalStratifiedLisseLattices | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassChern | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassCoefficients | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassDiagonal | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFinite | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassFiniteDiagonal | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassProjective | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassPullback | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassReduction | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassSystems | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TowerClassTwisting | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.TraceBaseChangeFirst | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.WeilTateTwistFrobenius | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.WfTateTwist | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.AdicScalarTraceCoherence | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.BaseChangeIdentityOpenRestriction | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.BrownHypothesesSmall | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.CommonFieldLatticeGenerators | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.FieldTensor | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralExtHomContinuity | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralModelsGenerators | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.LocallyClosedGeneratorTensorIntersection | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Existing interface and data unchanged; no adaptation. |
| Sheaf.Targets.PoincareTateBoundedConstructible | unclaimed | Existing interface and data unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing interface and data unchanged; no adaptation. |

## Status

landed 20261023T135436-L-2894854 2026-10-23 (merge of deliver/T8/WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization)
