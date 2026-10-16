# AlgebraicGeometry.ProEtale.condensedPullbackHom

## Reason

The reducible abbreviation expands the inverse-image adjunction construction while
checking coefficient transport. Making it an ordinary transparent definition preserves
its exact term, type and visibility while preventing eager reducible expansion. The
existing IsMonHom and IsIso instances remain its public API. Basic is unclaimed.
The second reader tested the final revised proof in a separate sandbox with the original
Basic: ContinuousLisseStratifiedLattices still exceeded the 60-second limit. With the
delivered Basic it compiled in approximately six seconds. No limit was raised and no
slow file was split. The two lattice obligations are separate mathematical steps.

The definition has exactly the same right-hand side. Reading its uses in coefficient
pullbacks and scalar extension therefore gives exactly the same mathematical objects,
including every target using those functors; no target type or meaning is changed.
This is a reducibility repair and can affect elaboration performance for consumers.
Individual current-source consumer checks and their limits are recorded in report.md;
unchanged slow or not-yet-built consumers are not claimed to have passed.

## Old

```lean
noncomputable abbrev condensedPullbackHom :
    (f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y) ⟶ condensedRingObj Λ X :=
  Functor.compAlgHom (upperStarFromPoint Y) (f)^*[Ab.{u + 1}] (upperStarFromPointComp f).hom Λ
```

## New

```lean
noncomputable def condensedPullbackHom :
    (f)^*[Ab.{u + 1}].obj (condensedRingObj Λ Y) ⟶ condensedRingObj Λ X :=
  Functor.compAlgHom (upperStarFromPoint Y) (f)^*[Ab.{u + 1}] (upperStarFromPointComp f).hom Λ
```

## Users

The table contains every current transitive consumer from
`tools/downstream.py WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic --uses
AlgebraicGeometry.ProEtale.condensedPullbackHom`, Basic itself, and the new modules of
this delivery. All consumers retain their mathematical signatures and meanings.
The local-triviality module remains unchanged; its private helpers are reused through
proof-only import all commands. No other consumer is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexColimit | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexCompatibility | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDerivedTransport | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexDiagram | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexModel | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexPresentation | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedCoefficientComplexUnderivedCompatibility | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedDerivedTensorComparison | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | unclaimed | Unchanged source and public interface; its existing private helpers are reused. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationCorank | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationEvaluation | B2 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.CondensedFieldPresentationMatrix | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldCokernelLocalFree | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ContinuousFieldPresentationNormalForm | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection | E2 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedClosedCostalkDerivedContinuity | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleExtensionTower | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleGenericLfp | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedConstructibleOneStep | J1 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedConstructiblePiece | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteFreeDerivedHom | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteFreeHomContinuity | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteFreeHomEvaluation | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteFreeInternalHomColimits | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteFreeTensorExact | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedFiniteModelImmersionRestriction | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedFinitePresentationDescent | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | B3 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedHypercoverComparison | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedHypercoverInjectiveRow | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedInternalHomSections | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedLfpCoefficientModel | A4 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedLfpHomContinuity | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedLocalPieceHomContinuity | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedLocalPresentationPullback | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedLocallyClosedExtensionTower | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedLocallyClosedOneStep | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedLocallyClosedPiece | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedOpenClosedRecollement | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedPointBasisEvaluation | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQbarFunctionPresentations | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQbarLfpCoverComposition | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | F4 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQcqsPushforwardContinuity | D3 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedQcqsPushforwardLocalComparison | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedSheafExtContinuity | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelAssembly | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStep | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepEmpty | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonempty | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyGluing | G1 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenClosed | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedStratumModelInductionStepNonemptyOpenPiece | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedSurjectiveClosedEquivalence | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.CondensedSurjectiveClosedLocalPresentation | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ConstructibleCokernelsExtensions | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousCoefficientRealizations | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | C4 | Assigned proof uses the same coefficient maps and pullback functors. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousFiniteEtaleLatticeDescent | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralCoefficientTelescope | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralCoefficients | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralComparisons | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeEquality | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeSourceAdjunct | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct | F2 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralPullComposition | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralPushComparison | B2 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousIntegralScalarExact | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ContinuousRegularFunctions | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | E4 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteRealizationFunctor | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.FiniteDiscreteSchemeRing | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.GeometricFieldProEtaleEvaluation | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.GeometricFieldProfiniteDenseSubsite | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleKernels | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleNakayama | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSerre | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralFiniteFreeContractive | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | D4 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixAnalyticCover | C1 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixEntryProperties | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralMatrixPivotCover | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralReductionConservative | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralReductionConstructible | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralReductionScalar | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralReductionTensor | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralReductionTriangulatedProperty | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralRegularRationalUnit | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralResidueComparisons | B4 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralResiduePerfect | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.IntegralScalarContractive | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.PointLanAffineEvaluation | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.PointLanFiniteProducts | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ProEtalePointComponentsMaps | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ProEtaleSheafificationWcontractibleSections | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ProfinitePointPullback | F1 | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.Paper.ProfiniteTestObjectFunctor | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| TargetsCheck | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic | unclaimed | abbrev becomes def; identical body, type and visibility. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility | F3 | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | A2 | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs | unclaimed | Unchanged statements, definitions and proofs; no adaptation needed. |

## Status

landed 20261016T064222-L-582225 2026-10-16 (merge of deliver/C4/Sheaf.Paper.ContinuousConstructibleIntegralStratum)
