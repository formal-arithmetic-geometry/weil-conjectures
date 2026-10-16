# boundedConstructiblePullbackSquareComparison

## Reason

The concrete left adjunct proof exceeds the 60-second limit when exporting artifacts
with the derived square-comparison body exposed. Hide that body behind the existing
component and adjunct APIs. Its definition, every signature, all source proofs and
public imports are preserved. This is the current source snapshot, including the
squareExchange presentation and the later component lemma, with one attribute added.
No target meaning changes and no semantic target review is reopened.

MorphismDefs and BoundedExchangeAmbient are unclaimed in the current shared checkout.
BoundedExchangeAmbient's original fails at line 163 because it uses the defining body
in a definitional equality. Add only a plain `import all` of MorphismDefs for that proof;
its existing public import, signatures and proofs stay unchanged. Its original compiler
error is recorded in the original delivery report. The landed global build also found
two local reducibility commands in ContinuousIntegralExchangeTargetAdjunct that tried
to mark the now-hidden comparison irreducible. Remove that name from both commands: a
hidden body already prevents unfolding, and Lean cannot change its reducibility from
this ordinary import. The consumer continues to use the component and adjunct APIs.
No mathematical construction, compiler limit, or kernel check changes.

## Old

```lean
noncomputable def boundedConstructiblePullbackSquareComparison (sq : CommSq g' f' f g) :
    boundedConstructibleUpperStar Λ ℓ k g ⋙ boundedConstructibleUpperStar Λ ℓ k f' ≅
      boundedConstructibleUpperStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g' :=
  (boundedConstructibleUpperStarComp Λ ℓ k f' g).symm ≪≫
    eqToIso (by simp only [sq.w]) ≪≫ boundedConstructibleUpperStarComp Λ ℓ k g' f
```

## New

```lean
@[no_expose]
noncomputable def boundedConstructiblePullbackSquareComparison (sq : CommSq g' f' f g) :
    boundedConstructibleUpperStar Λ ℓ k g ⋙ boundedConstructibleUpperStar Λ ℓ k f' ≅
      boundedConstructibleUpperStar Λ ℓ k f ⋙ boundedConstructibleUpperStar Λ ℓ k g' :=
  (boundedConstructibleUpperStarComp Λ ℓ k f' g).symm ≪≫
    eqToIso (by simp only [sq.w]) ≪≫ boundedConstructibleUpperStarComp Λ ℓ k g' f
```

BoundedExchangeAmbient additionally gains this proof-only import:

```lean
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
```

ContinuousIntegralExchangeTargetAdjunct additionally removes the hidden comparison from
both local reducibility commands (original lines 378–380 and 402–404):

```lean
-- Old (twice)
attribute [local irreducible] Adjunction.homEquiv
  boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarLowerStarAdjunction boundedConstructiblePullbackSquareComparison
-- New (twice)
attribute [local irreducible] Adjunction.homEquiv
  boundedConstructibleUpperStar boundedConstructibleLowerStar
  boundedConstructibleUpperStarLowerStarAdjunction
```

Its imports, declaration signatures, visibility, proof terms and docstrings are unchanged.

## Users

The table includes every module listed by `tools/downstream.py` for the changed source,
plus this delivery's new users. All five direct textual users were inspected.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldEvaluationFunctors | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldRegularModuleScalars | B4 | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Forced proof access: add plain import all; original fails, adapted compiled. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleOneStep | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleOpenClosedImages | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteCoefficientLocalization | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteModelExtensions | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteModelProofAPI | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Uses comparison and preserved adjunct API; compiled in delivery. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | unclaimed | Comparison body not used; public edge helper reused by normal proof import. |
| Sheaf.Paper.CondensedQbarFunctionCoefficients | B3 | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedQbarPullbackCube | unclaimed | Uses comparison and preserved adjunct API; compiled in delivery. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousChartSchemeNaturality | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | B2 | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousFiniteFreeDenominators | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousFiniteFreeKernelModel | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Uses naturality and the preserved adjunct API; source unchanged. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | unclaimed | Forced adaptation: remove the hidden comparison from two local irreducible commands; component and adjunct proofs unchanged. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationCounit | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralUnderivedPushComparison | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionLocalModel | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalModel | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionRationalization | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitData | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousLatticeIntersectionSplitModel | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | H2 | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralLfpLocalTorsionCharts | A4 | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixAnalyticData | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixFunctionsPullback | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixKernelLocallyFree | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixPointwiseRank | E4 | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixZeroNeighborhood | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralRegularCoefficientPullback | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | No signature or construction change; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No signature or construction change; no adaptation needed. |
| TargetsCheck | unclaimed | No signature or construction change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No signature or construction change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Passes the comparison as data; source unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Add only no_expose to the unchanged square comparison. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No signature or construction change; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | No signature or construction change; no adaptation needed. |

## Status

landed 20261016T095751-L-2157226 2026-10-16 (merge of deliver/XR0d56945a24047e2a/Sheaf.Paper.CondensedQbarExchangeEquality)
60149c8e224e3c62533b5256beef7d956832ce0e; awaiting independent reader.
