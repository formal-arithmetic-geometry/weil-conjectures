# AlgebraicGeometry.ProEtale.condensedPushforwardHom

## Reason

Sectionwise kernel checks exceeded the 60-second limit when reducing concrete coefficient adjunction and pullback constructions. Expose the exact construction through proved equality APIs. This changes computation, not mathematical meaning. Witnesses are chosen only from proved statements specifying exact equality to the original construction. No hollow data, new assumptions, or axiom is introduced. All existing signatures and visibility are retained. Target meaning is unchanged; reviewers should check the equality APIs when renewing the definition review.

## Old

```lean
noncomputable def condensedPushforwardHom :
    condensedRingObj Λ Y ⟶ (f)_*[Ab.{u + 1}].obj (condensedRingObj Λ X) :=
  (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unitAlgHom (condensedRingObj Λ Y) ≫
    (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f)

```

## New

```lean
theorem condensedPushforwardHom_exists :
    ∃ e : (condensedRingObj Λ Y ⟶ (f)_*[Ab.{u + 1}].obj (condensedRingObj Λ X)), e =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app (condensedRingObj Λ Y) ≫
    (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f) :=
  ⟨_, rfl⟩

/-- The canonical coefficient map, kept behind its exact equality API. This avoids
unfolding the inverse-image adjunction when checking sectionwise calculations.
The proved equality specifies the witness uniquely. -/
noncomputable def condensedPushforwardHom :
    condensedRingObj Λ Y ⟶ (f)_*[Ab.{u + 1}].obj (condensedRingObj Λ X) :=
  Classical.choose (condensedPushforwardHom_exists Λ f)

omit [MonObj Λ] in
/-- The coefficient map is the explicit unit followed by the image of the comparison. -/
theorem condensedPushforwardHom_def :
    condensedPushforwardHom Λ f =
      (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f).unit.app (condensedRingObj Λ Y) ≫
    (f)_*[Ab.{u + 1}].map (condensedPullbackHom Λ f) :=
  Classical.choose_spec (condensedPushforwardHom_exists Λ f)

```

The defining-equation API also supplies this proved composition law:

```lean
lemma unit_comp_map_condensedPushforwardHom :
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y)).unit.app
        (pointUpperStar.obj Λ) ≫
      (toSpecZ Y)_*[Ab.{u + 1}].map (condensedPushforwardHom Λ f) =
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X)).unit.app
        (pointUpperStar.obj Λ) ≫
      (eqToHom (congrArg (lowerStar Ab.{u + 1}) (comp_toSpecZ f).symm)).app _ ≫
        (lowerStarComp Ab.{u + 1} f (toSpecZ Y)).inv.app
          ((toSpecZ X)^*[Ab.{u + 1}].obj (pointUpperStar.obj Λ)) := by
  rw [condensedPushforwardHom_def, condensedPullbackHom_eq]
  exact unit_comp_lowerStar_map_unit_comp_upperStarComp Ab.{u + 1}
    f (toSpecZ X) (toSpecZ Y) (comp_toSpecZ f) (pointUpperStar.obj Λ)
```

## Users

All modules listed by tools/downstream.py --uses are included below. Four unclaimed consumers replace explicit unfolding with the defining equation; two also rewrite that equation before using an adjunction square. Their original failures and adapted compilations are recorded in the report.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | unclaimed | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedCoefficientFamilyHomStage | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedCoefficientHomStage | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedConstructibleGenericLfp | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedConstructiblePiece | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteFreeDerivedHom | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteFreeHomContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteFreeHomEvaluation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteFreeInternalHomColimits | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteFreeTensorExact | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteModelImmersionRestriction | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFinitePresentationMatrices | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedFpHomStage | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedHypercoverComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedHypercoverInjectiveRow | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedInternalHomSections | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLfpCoefficientModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLocalCoefficientAdjoints | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLocalModelGluing | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLocalPresentationPullback | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedLocallyClosedPiece | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarExchangeEquality | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarLfpCoverComposition | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQbarScalarPullback | unclaimed | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedQcqsPushforwardLocalComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedSurjectiveClosedEquivalence | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedSurjectiveClosedLocalPresentation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.CondensedUnderivedPushforwardContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralCoefficientTelescope | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralCoefficients | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralDerivedUnit | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralScalarExact | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersection | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousLocallyFreePullback | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteCoefficientSections | D3 | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.FiniteDiscreteSchemeRing | unclaimed | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.GeometricFieldProfiniteDenseSubsite | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | unclaimed | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralReductionScalar | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralReductionTensor | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralReductionTriangulatedProperty | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueComparisonInterface | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueOrdinaryMonoidal | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResiduePerfect | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResiduePullSquare | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResiduePullbackPreservesFlat | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.InverseImageModuleFlat | claimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ModuleObjectFreeGenerators | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.PointLanAffineEvaluation | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.PointLanFiniteProducts | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ProEtalePointComponentsMaps | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ProEtaleSheafificationWcontractibleSections | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ProfinitePointPullback | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.ProfiniteTestObjectFunctor | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.Paper.SplitProEtaleModuleProductMap | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic | unclaimed | Exact equality preserves all statements and mathematical constructions. Delivered; proof uses the equality API. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | claimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs | unclaimed | Exact equality preserves all statements and mathematical constructions. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs | unclaimed | Exact equality preserves all statements and mathematical constructions. |

## Status

landed 20261016T171806-L-1680950 2026-10-16 (merge of deliver/D3/Sheaf.Paper.FiniteDiscreteCoefficientSections)
