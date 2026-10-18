# CategoryTheory.abelianSheaf_complex_colimit_homotopyColimit and moduleSheaf_complex_colimit_homotopyColimit

## Reason

The completed proofs use private generic category helpers. Their extra universe name
is conservatively classified as an interface command change by stage-3 preflight.
This record documents that command change. Both existing public theorem signatures,
visibility, and all four original public imports are unchanged. No existing public
definition is changed. All newly added private helpers are fully proved.

## Old

```lean
universe w u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex
```

The two existing theorem bodies were `by sorry`.

## New

```lean
universe w u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex CochainComplex.HomComplex
```

The new universe `v` occurs only in private generic helpers, whose category hom
universes are independent of their object universes. It does not occur in either
existing public signature. The helpers construct the telescope cokernel and short
exact sequence, the derived coproducts, and the transported distinguished triangles.
The two existing theorem bodies are complete proofs with no added hypotheses.

The separately delivered new module `Sheaf.CategoryTheory.SequentialTelescopeMono`
has the new public theorem `CategoryTheory.sequentialTelescope_mono`, with its own DAG
node. Its private coordinate helpers are fully proved. The local-instance attributes
in that new module are file-local. The item imports this module only for its proof.

## Users

The read-only `tools/downstream.py` check found the following transitive importers.
Neither existing theorem name occurs in any downstream module yet. Their existing
signatures, mathematical meanings, and dependencies on public definitions are unchanged.
No downstream module needs an adaptation, and no target statement needs reopening.
The holder of a module that is not adapted was not queried.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit | D4 | Two proofs completed; signatures unchanged. |
| Sheaf.CategoryTheory.SequentialTelescopeMono | D4 | New proved lemma and private helpers. |
| Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicBoundedConstructibleProperAdjoint | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EllAdicProperLocalizingPushforward | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.OpenDirectImageOverField | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothGenericDirectImage | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.CategoryTheory.ThreeStepAdjunctionComparison | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.BoundedExchangeAmbient | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CoefficientDerivedFunctorAPI | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedCoefficientComparisons | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedConstructibleOneStep | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFiniteFamilyHomDescent | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFiniteLocalSubmodules | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFiniteModelExtensions | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFinitePresentationDescent | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedLfpCoefficientModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedLfpHomContinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedLocalModelGluing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedOpenClosedRecollement | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarCoefficientConstruction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarComparisons | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarExchangeEquality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarFieldCoefficientSquare | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarFieldEvaluationLinearity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarFieldFiberExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarFieldPointCoefficientValue | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarPullbackCube | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedQbarScalarPullback | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedSheafExtContinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedStratumModelAssembly | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStep | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousCoefficientModuleEncoding | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousCoefficientRealizations | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousConstructibleIntegralTransport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralComparisons | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralPullComposition | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralPushComparison | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLatticeFiniteCoproduct | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLisseCoefficientDescent | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLissePullbackSystem | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLisseStratumDescent | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousLocallyFreePullback | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingRestriction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingScalarExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousModuleEncodingSliceFreeness | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.ContinuousRegularFunctions | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientCoherentPullbacks | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageConjugation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientDirectImageOrigin | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientEncoding | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientPullbackIso | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestriction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientRestrictionCoherence | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientSheafComposition | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteCoefficientSquareCoherence | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleEncoding | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteConstructibleLocalPiece | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteEncodedPresentation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteDiscreteRestrictionEncoding | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.FiniteEtaleLocallyFreeModels | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralConstructibleKernels | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralConstructibleNakayama | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralConstructibleSerre | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralConstructibleSheafHom | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralExchangeReduction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralFiniteFreeContractive | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralLfpHomContinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixAnalyticData | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixCoefficientTransport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixEntryProperties | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixPivotCover | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralReductionConservative | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralReductionConstructible | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralRegularRationalUnit | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralResidueExchange | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.Paper.IntegralScalarContractive | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.PoincareDuality.CompatibleIntegralRootBases | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.PoincareDuality.CompatiblePrimitiveRoots | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.PoincareDuality.IntegralResidueLimit | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.PoincareDuality.IntegralResidueQuotient | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.PoincareDuality.IntegralTateBasis | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.PoincareDuality.IntegralTateLocalLine | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.PoincareDuality.ProperProjectionFormulaBounded | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.PoincareDuality.TateTwistOneLocalLine | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeSection | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.SmoothPurity.NormalizedWitness | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.WeilSheaf.AffineCurveRangePositive | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricConjugacy | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.WeilSheaf.CohomologyGeometricEquivalence | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | not queried; not adapted | Existing public signatures and definitions unchanged. |
| Sheaf.WeilSheaf.FiniteBoundaryPositive | not queried; not adapted | Existing public signatures and definitions unchanged. |
| TargetsCheck | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Defs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DenseOpen | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStratification | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.DeligneLaumon.Reduction.Weights | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Reciprocity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Pairing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.TraceIsomorphism | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.PoincareDuality.Transport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalPolynomial | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafRepresentation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Basic | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Deformation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.FamilyObject | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Normalization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Orientation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Reduction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionProduct | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionReduction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Trace | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Transport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.ArtinSchreierVanishing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Convolution | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.KernelTransform | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Transform | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.Unit | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.AffineSpace.UnitVanishing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.ArtinSchreierCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Composition | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Defs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Inversion | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Perverse | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseChange | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.BaseLinear | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.FourierTransform.Properties.Stalk | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.PoincareDuality.Poincare | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.PoincareDuality.ProjectionFormula | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.PoincareDuality.Verdier | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ClosedImmersionStages | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Adjunctions | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Finiteness.Kunneth | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Duality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHomGeneric | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GenericPerfect | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ClosedImmersion | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryCompactSupport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OrdinaryProper | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ProperProjectionFormula | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Orientation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Package | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.PointBiduality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RationalStage | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHom | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.Matrix | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriekConstructible | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.UpperShriekOpenRestriction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.VerdierPreservation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplex | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexInternalHom | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Derived.WeilComplexTensorHom | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.ClosedSupport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.Localization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.DualPerfect | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionExtendScalars | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Stability | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleAdditive | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.SmoothPurity.Defs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.Statement | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Basic | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Basic | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Correspondence | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Dualizing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.FixedPoint | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Frobenius | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Main | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Slop.Stalk | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.TraceFormula.Statement | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.Defs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.TensorHom | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilObject.BoundedConstructible.UpperLowerStar | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierDual | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierFrobenius | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierPurity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ArtinSchreierTrace | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.BoundaryStalk | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Cohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.CohomologyExact | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.CohomologyShift | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ComplexWeights | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ConstantTwistCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Curve | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.CurveEndpoints | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Defs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.DenseOpen | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.DirectImageRestriction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.DirectImageStalk | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ExtensionByZero | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FiniteEtaleLisse | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Finiteness | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Fourier | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Defs | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.TensorLisse | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.UpperStar | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierPlancherel | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist.ConstantTwist | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTateTwist.Transform | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTrace | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.FourierTraceAux | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.GeometricCoinvariants | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.GeometricallyConstant | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.HomologyShift | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LFunction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Localization | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LocalizationRational | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerShriek | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStar | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStarComp | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStarId | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStarPairing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.LowerStarTensorPow | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.MiddleExtension | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.OpenImmersion | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.OpenImmersionRestriction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Operations | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.PoincareDuality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology.LowerShriek | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.ProperCohomology.OpenImmersion | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.RealPurity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Realizable | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkConstantTwist | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkExtensionByZero | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkInternalHom | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkOpenImmersion | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkTateTwist | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.StalkTensor | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TateTwist | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TateTwistCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.Tensor | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TensorObjPairing | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TensorPower | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionCongr | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionOps | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceFunctionTensor | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.TraceSeries | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.WeilSheaf.UpperStarPointwise | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.Examples | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.HasseWeil | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.Rationality | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.RelativePurity | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.SixOperations | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.SmoothProper | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.TraceFormula | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried; not adapted | Existing public signatures and definitions unchanged. |
| WeilConjectures.ZetaFunction.Weights | not queried; not adapted | Existing public signatures and definitions unchanged. |

## Status

landed 20261018T062724-L-640105 2026-10-18 (merge of deliver/D4/Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit)
