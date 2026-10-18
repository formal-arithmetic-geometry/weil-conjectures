# AlgebraicGeometry.Etale.finiteLisseDualPullbackComparison

## Reason

The original transpose unfolds the concrete derived tensor/closed structure when
its isomorphism proof is specialized to coefficient modules. The profiler reports
kernel comparisons of the derived tensor functor, exceeding the file limit. This is
the instance-comparison problem documented in
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`.

Factor the same morphism through the general strong-monoidal internal-Hom
comparison followed by the mapped coefficient-unit comparison. The new generic
`derivedHomPullbackAlongIsoComparison` packages this composition without comparing
concrete derived monoidal instances. The proved private theorem
`derivedHomPullbackAlongIsoComparison_eq_transpose` identifies it with exactly the
old transpose by naturality of the tensor-Hom adjunction and the tensor comparison's
inverse law. The private theorem `finiteLisseDualPullbackComparison_isIso` freezes the resulting
API over an abstract coefficient ring before its prime-field specialization.
No chosen object, arbitrary witness, or additional mathematical
hypothesis enters the map. Every existing signature is unchanged.

## Old

```lean
noncomputable def finiteLisseDualPullbackComparison
    {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C : DerivedCategoryModule Λ T) :
    (L(upperStar (ModuleCat.{u + 1} Λ) v)).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) T).obj (op C)).obj (constantComplex Λ T)) ⟶
      ((derivedHom (ModuleCat.{u + 1} Λ) T').obj
        (op ((L(upperStar (ModuleCat.{u + 1} Λ) v)).obj C))).obj (constantComplex Λ T') :=
  (derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ)
      ((L(upperStar (ModuleCat.{u + 1} Λ) v)).obj C)).homEquiv _ _
    ((leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) v C
        (((derivedHom (ModuleCat.{u + 1} Λ) T).obj (op C)).obj
          (constantComplex Λ T))).inv ≫
      (L(upperStar (ModuleCat.{u + 1} Λ) v)).map
        ((derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) C).counit.app
          (constantComplex Λ T)) ≫
      (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) v).hom)
```

## New

```lean
noncomputable def finiteLisseDualPullbackComparison
    {Λ : Type (u + 1)} [CommRing Λ] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (C : DerivedCategoryModule Λ T) :
    (L(upperStar (ModuleCat.{u + 1} Λ) v)).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) T).obj (op C)).obj (constantComplex Λ T)) ⟶
      ((derivedHom (ModuleCat.{u + 1} Λ) T').obj
        (op ((L(upperStar (ModuleCat.{u + 1} Λ) v)).obj C))).obj (constantComplex Λ T') :=
  derivedHomPullbackAlongIsoComparison v C (constantComplex Λ T) (constantComplex Λ T')
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) v)
```

The generic helper definition and its transpose identity are in the same item
module. The item's theorem statement is unchanged. The mathematical map, hence
any target meaning involving it, is unchanged by this refactoring.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FiniteLisseFieldDual --uses
finiteLisseDualPullbackComparison` found the item as its only textual user. The
387 transitive importers are also listed below; none mentions the comparison.
No external module is adapted. The sole direct importer is
`Sheaf.AlgebraicGeometry.SmoothGenericDirectImage`; it imports the category
interfaces it needs explicitly, and its unchanged source compiled against the
new item in 9.4 seconds.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.FiniteLisseFieldDual` | A7 | Body refactored; signature unchanged; theorem proved from local models. |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility` | X2 | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility` | H3 | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients` | X3 | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.OpenDirectImageOverField` | B4 | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.AlgebraicGeometry.SmoothGenericDirectImage` | S1 | No textual use of the map; statement and proof unchanged. |
| `Sheaf.CategoryTheory.ThreeStepAdjunctionComparison` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.BoundedExchangeAmbient` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CoefficientDerivedFunctorAPI` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CoefficientExchangeFromComparisons` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedClosedCostalkDerivedContinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedCoefficientComparisons` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedConstructibleExtensionTower` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedConstructibleOneStep` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedConstructibleOpenClosedImages` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedFiniteCoefficientLocalization` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedFiniteFamilyHomDescent` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedFiniteLocalSubmodules` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedFiniteModelExtensions` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedFiniteModelProofAPI` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedFinitePresentationDescent` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedFlatCoefficientCalculus` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedLfpCoefficientModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedLfpHomContinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedLocalModelGluing` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedLocalPieceCostalkModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedLocalPieceHomContinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedLocallyClosedExtensionTower` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedLocallyClosedOneStep` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedOpenClosedRecollement` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarBaseChangeCompatibility` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarCoefficientConstruction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarComparisons` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarExchangeEquality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarExchangeLeftAdjunct` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarExchangeRightAdjunct` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarFieldCoefficientSquare` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarFieldEvaluationLinearity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarFieldFiberExtension` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarFieldPointCoefficientValue` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarFunctionCoefficients` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarFunctionPresentations` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarLfpLocalTriviality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarLfpMatrixRefinement` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarPullbackCube` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedQbarScalarPullback` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedSheafExtContinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedStratumModelAssembly` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedStratumModelInductionStep` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedStratumModelInductionStepEmpty` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonempty` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ConstructibleCokernelsExtensions` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousAffineEtaleLattice` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousChartSchemeNaturality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousCoefficientModuleEncoding` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousCoefficientRealizations` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralDenominators` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralGluing` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralImage` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralSingle` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralStratum` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousConstructibleIntegralTransport` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousEtaleLocalLattices` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousExchangeIntegralModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousFiniteFreeDenominators` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousFiniteFreeKernelModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralComparisons` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralComplexTelescope` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralExchangeEquality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralExchangeSquare` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralLocalization` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralLocalizationContinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralLocalizationCounit` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralLocalizationHomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralLocalizationLegs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralLocalizationMate` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralLocalizationModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralModuleTelescope` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralPullComposition` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralPushComparison` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralRegularTelescope` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousIntegralUnderivedPushComparison` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLatticeFiniteCoproduct` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLatticeIntersectionLocalModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLatticeIntersectionRationalization` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitData` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLatticeIntersectionSplitModel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLisseCoefficientDescent` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLissePullbackSystem` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLisseStratifiedLattices` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLisseStratumDescent` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousLocallyFreePullback` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousModuleEncodingLattices` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousModuleEncodingLocalFreeness` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousModuleEncodingRestriction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousModuleEncodingScalarExtension` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousModuleEncodingSliceFreeness` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.ContinuousRegularFunctions` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientEncoding` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientExchange` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientRestriction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteConstructibleEncoding` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteDerivedCoefficientData` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteEncodedPresentation` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteExchangeComparison` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteExchangeRealization` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteRealizationFunctor` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteDiscreteRestrictionEncoding` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.FiniteEtaleLocallyFreeModels` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralConstructibleKernels` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralConstructibleNakayama` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralConstructibleSequentialHom` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralConstructibleSerre` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralConstructibleSheafHom` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralExchangeReduction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralFiniteExchangeComparison` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralFiniteFreeContractive` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralLfpEventualFreeImage` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralLfpFiniteQuotientCharts` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralLfpHomContinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralLfpLocalTorsionCharts` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralLfpLocallyFreeResolution` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixAnalyticCover` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixAnalyticData` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixCoefficientTransport` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixEntryProperties` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixFunctionsPullback` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixKernelLocallyFree` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixPivotCover` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixPointwiseRank` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralMatrixZeroNeighborhood` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralReductionConservative` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralReductionConstructible` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralRegularCoefficientPullback` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralRegularRationalUnit` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralResidueExchange` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralResidueExchangeAlgebra` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.Paper.IntegralScalarContractive` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.PoincareDuality.CompatibleIntegralRootBases` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.PoincareDuality.CompatiblePrimitiveRoots` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.PoincareDuality.IntegralResidueLimit` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.PoincareDuality.IntegralResidueQuotient` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.PoincareDuality.IntegralTateBasis` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.PoincareDuality.IntegralTateLocalLine` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.PoincareDuality.TateTwistOneLocalLine` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.SmoothPurity.NormalizedWitness` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.WeilSheaf.AffineCurveRangePositive` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.WeilSheaf.CohomologyGeometricEquivalence` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `Sheaf.WeilSheaf.FiniteBoundaryPositive` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `TargetsCheck` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` | B3 | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.Defs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.DenseOpen` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealPushforward` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.CompactSupport` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.FibreCohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMap` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.FormalSteps` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.RealCurve` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.DeligneLaumon.Reduction.Weights` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.FourierTransform.Perverse` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.PoincareDuality.Poincare` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.PoincareDuality.Verdier` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ClosedImmersionStages` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.Etale.Derived.RationalStage` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.Etale.Perverse.Operations` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.Localization` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | B2 | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.SmoothPurity.Defs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.Statement` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Basic` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Slop.Basic` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Slop.CompactCohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Slop.Correspondence` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Slop.Dualizing` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Slop.FixedPoint` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Slop.Frobenius` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Slop.Main` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Slop.Stalk` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.TraceFormula.Statement` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilObject.BoundedConstructible.Defs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilObject.BoundedConstructible.TensorHom` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ArtinSchreierDual` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ArtinSchreierFrobenius` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ArtinSchreierPurity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ArtinSchreierTrace` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.BoundaryStalk` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Cohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.CohomologyExact` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.CohomologyShift` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ComplexWeights` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ConstantTwistCohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Curve` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Defs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.DenseOpen` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.DirectImageRestriction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.DirectImageStalk` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ExtensionByZero` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FiniteEtaleLisse` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Finiteness` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Fourier` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion.Defs` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion.TensorLisse` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion.UpperStar` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierPlancherel` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierTateTwist` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierTateTwist.Transform` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierTrace` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.FourierTraceAux` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.GeometricCoinvariants` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.GeometricallyConstant` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.GrothendieckLefschetz` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.HomologyShift` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LFunction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Localization` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LocalizationRational` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LowerShriek` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LowerStar` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LowerStarComp` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LowerStarId` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LowerStarPairing` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.LowerStarTensorPow` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.MiddleExtension` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.OpenImmersion` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.OpenImmersionRestriction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Operations` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.PoincareDuality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ProperCohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.RealPurity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Realizable` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.StalkConstantTwist` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.StalkExtensionByZero` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.StalkInternalHom` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.StalkOpenImmersion` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.StalkTateTwist` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.StalkTensor` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TateTwist` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TateTwistCohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.Tensor` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TensorObjPairing` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TensorPower` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TraceFunctionCongr` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TraceFunctionOps` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TraceFunctionTensor` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.TraceSeries` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.WeilSheaf.UpperStarPointwise` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.CohomologicalFamily` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.Rationality` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.TraceFormula` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | No textual use of the map; statement and proof unchanged. |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | No textual use of the map; statement and proof unchanged. |

## Status

landed 20261018T071133-L-1663245 2026-10-18 (merge of deliver/A7/Sheaf.AlgebraicGeometry.FiniteLisseFieldDual)
