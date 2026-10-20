# WeilConjectures.coefficientHomComponent

## Reason

Use the existing `homComplexπ` projection API instead of exposing the nested
`homComplex_exists.choose_spec.choose` term in this wrapper. The two expressions
are definitionally equal: after unfolding the two projection definitions, `rfl`
checks their equality. The diagnostic kernel check took 39.6 seconds; repeated
conversion in the bidual construction exceeded the file limit. Using the
projection API makes that conversion unnecessary. No mathematical data,
hypotheses, conclusions, declaration signatures, or existing attributes change.
The independently landed module publicly imports `HomComplexComponents`, which defines the API.
The attached definition node records this API dependency. Targets using the
definition require the normal independent definition review; their meaning stays
unchanged because the old and new expressions are definitionally equal.

## Old

```lean
noncomputable def coefficientHomComponent
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex.{c, v, max c v u, max c v u} (R := A) L M).X n ⟶
      SheafOfModules.homObj (R := A) (L.X p) (M.X q) :=
  (homComplex_exists.{c, v, max c v u, max c v u}
    (R := A)).choose_spec.choose L M n p q h
```

## New

```lean
noncomputable def coefficientHomComponent
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex.{c, v, max c v u, max c v u} (R := A) L M).X n ⟶
      SheafOfModules.homObj (R := A) (L.X p) (M.X q) :=
  homComplexπ.{c, v, max c v u, max c v u} (R := A) L M n p q h
```

## Users

Refreshed against the current shared source after the return of head `793a42702`.
The table retains the earlier downstream inventory and adds every currently
reported downstream module and direct declaration user from
`tools/downstream.py Sheaf.Paper.CoefficientHomRepresentativeEvaluation
--uses coefficientHomComponent`. In particular,
`Sheaf.Algebra.Homology.RingedSliceEvaluationModels` uses the projection twice
in `RingedSliceHomModel`, for the site and its slice. Both references keep the
same chosen projections and formula; no adaptation is needed. Its unchanged
source compiled successfully through `lcompile.py` in 14.5 seconds.

The projection refactor has independently landed since the original packet
(see `coord/changes/coefficientHomComponentProjectionAPI.md`). This repaired
packet preserves the current projection module and its private native-API
compatibility lemma verbatim. It does not replace either with the older overlay.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.AlgebraicShriekDerivedHomAdjunction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.CompleteLocalCoherentDuality | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.DerivedCoinductionAdjunction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.DerivedEvaluationCanonicalMap | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.DerivedEvaluationFiniteInjective | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.DerivedEvaluationPseudoCoherent | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel | K5 | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.PerfectAlgebraCoinductionTensor | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RhomHypercohomologyBridgeOfUniverses | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedDerivedTensorNative | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedInternalHomExactUniverses | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedSiteStrictPerfectHom | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedSliceEvaluationCoherence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedSliceEvaluationModels | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedSliceEvaluationTranspose | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedSliceKoszulCoherence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedSliceRepresentativeEvaluation | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.RingedTensorComplexConstraints | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarHomCanonicalIso | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarHomExtensionKFlat | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarHomOrdinaryTensorComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarHomTensorCoherence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarHomTensorComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarInternalHomAdjunction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarInternalHomData | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarInternalHomTowerCoherence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarTensorComparisonTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.ScalarTensorTowerComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Algebra.Homology.SemidualizingRHomConservative | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedBaseChangeArrowLocalization | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedBasisBbdDescent | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedHomSheafComparisonLisse | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedScalarExtensionLocalSystems | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGenericEvaluationCoherence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleGenericExchangeAlgClosed | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleInternalHomLocalization | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleLocalDualInterval | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleOriginProperOpenInterchange | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.EtaleTwistedBidualTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.OrdinaryEtaleCupFunctoriality | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.ProperCompositionSiteTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.RelativeDualizingPairRigidity | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.SupportedProductLocalization | J8 | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.VaryingRingOperations | R5 | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting | Q2 | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.ClosedScalarHomComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.ClosedScalarHomComposition | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.ClosedScalarHomTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility | Q7 | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.DerivedBaseChangeMap | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.DerivedCategory.PerfectComplexDerivedBiduality | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.RelativeBidualTriangles | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.RingedEquivalenceLocalTests | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.RingedEquivalenceModuleHom | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.RingedPresentationTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.RingedSiteDualityMaps | Z6 | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.RingedSitePerfectDuality | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.CategoryTheory.Sites.ContractibleDerivedSectionsTensor | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.AdicSuppliedModelFlatCriterion | K4 | Same statement and data; no adaptation required. |
| Sheaf.Paper.AugmentedCechTensorPullback | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CanonicalRingedRefinementShape | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CanonicalRingedRefinementSquare | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefDerivedSystemEvaluationCalculus | U8 | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefficientCochainTensorCurry | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefficientExtensionReductionModel | Y2 | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefficientHomRepresentativeEvaluation | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefficientHomZeroClass | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefficientRingedSequenceSite | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefficientRingedTensorHomModel | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefficientTensorCurryNormalization | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CoefficientTwistsDetailed | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompatibleFiniteDerivedTrivializations | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedBaseChangeMap | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedConstantPresentationTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedDirectImageLimits | P5 | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedFiniteReductionTensorComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedFiniteReductionTensorModel | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedKoszulConstantTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedKoszulQuotientComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedProjectionCoherence | D2 | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedPullback | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedPullbackTriangles | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedPullbackUnitTower | V1 | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedScalarShift | F3 | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedTowerCompatibility | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.CompletedTowerCorners | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.ConstructibleFlatCohomologyTorBound | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.ConstructibleRHomCoproductContinuity | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.DeltaProperPushforward | S7 | Same statement and data; no adaptation required. |
| Sheaf.Paper.DeltaRestriction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.DerivedAutomorphismHomEvaluation | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.DerivedCompleteOnSlices | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.DerivedInternalHomFilteredColimit | R6 | Same statement and data; no adaptation required. |
| Sheaf.Paper.DualizingLocallyClosedInheritance | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.EtaleGeometricBiduality | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.EtaleIntegralLineDerivedComplete | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.EtaleProEtaleScalarMate | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.EvenLineHomShift | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.ExternalRHomConePairing | J7 | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientDirectImage | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteCoefficientDualConstructible | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteCompactSupportConstructibility | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteCompactSupportScalarComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteCompactSupportScalarTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteExceptionalInternalHom | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteFreeCompletedScalarComparison | V8 | Same statement and data; no adaptation required. |
| Sheaf.Paper.FinitePerfectAdicRealization | A4 | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteProjectiveTensorProducts | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteReductionReconstructionCompleted | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.FourArrows | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.HomUniversalCoefficients | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralDerivedOperationsOnSlices | V9 | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralHomAugmentedTowerComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralHomComparisonIsIso | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralHomModelsExist | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralHomReduction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralHomReductionComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralHomReductionModels | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralHomReductionTowerComponents | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralHomRoosTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralLineTensorComparison | H2 | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralOperationsPreserveConstructible | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.IntegralOperationsScalarComparisons | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.InternalSectionDerivedTensorComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.InternalSectionTotalComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.InternalSliceDerivedHomComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.LevelwiseAdicTruncations | K2 | Same statement and data; no adaptation required. |
| Sheaf.Paper.LisseNormalizedTowerLocalModels | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.NormalizedDVREffectivity | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.NormalizedDerivedIsomorphismSectionReduction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.NormalizedDerivedIsomorphismTransport | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.PbcActualStrictPullback | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.PbcUniformLocalModelCohomology | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.PointDerivedHomEvaluation | A8 | Same statement and data; no adaptation required. |
| Sheaf.Paper.PointReductionUnitNormalization | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.PointReductionUnits | A9 | Same statement and data; no adaptation required. |
| Sheaf.Paper.PointSectionsDerivedReduction | A6 | Same statement and data; no adaptation required. |
| Sheaf.Paper.PointSectionsFiniteReduction | R1 | Same statement and data; no adaptation required. |
| Sheaf.Paper.PointSectionsFiniteness | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.PointSectionsScalarExtension | G3 | Same statement and data; no adaptation required. |
| Sheaf.Paper.PointSectionsTensorShift | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.ProEtaleCompositionTowerNormalization | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.ProEtaleConstantReductionTower | B3 | Same statement and data; no adaptation required. |
| Sheaf.Paper.ProperOpenCoefficientMate | U3 | Same statement and data; no adaptation required. |
| Sheaf.Paper.PurReductionLimitShiftAdjunction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.PurTwistSheafLocallyFree | Q6 | Same statement and data; no adaptation required. |
| Sheaf.Paper.QuotientCornerFrobeniusStructures | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RationalSliceCompletedEvaluation | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedCoefficientAssociatorShifts | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedCoefficientProjectionCocycle | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedCoefficientProjectionData | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedCoefficientPullbackCoherence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedCoefficientPullbackComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedCoefficientPullbackShifts | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedCoefficientScalarShifts | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedCoefficientScalarUnits | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedDerivedSliceData | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedDerivedSliceLocalization | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedPushforwardCompletion | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedRefinementClopen | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedRefinementCoefficientSquare | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedRefinementConstruction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedRefinementCore | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedRefinementData | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedRefinementFinite | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedSliceDerivedAdjunction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedSliceDerivedComparisons | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedSliceDerivedMate | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.RingedSliceLocalizationModel | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SemilinearDerivedCalculus | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SemilinearDerivedSections | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SemilinearGeometryCore | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SemilinearGeometryDerived | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SemilinearGeometryOps | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SemilinearOperationsExistence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SemilinearSystemModels | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SemilinearSystemsExistence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SfHomTriangulated | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SfIntegralDirectImageConstructible | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SfRationalLocalGlobalPowerTorsion | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SignedLineTensorEquivalence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SpecifiedHomScalarEvaluation | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.StratumAmbientHom | V3 | Same statement and data; no adaptation required. |
| Sheaf.Paper.StrictTowerExchangeMateNormalization | N2 | Same statement and data; no adaptation required. |
| Sheaf.Paper.SystemCochainTensorReduction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SystemEvaluationFlat | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SystemNormalizedTensorClosure | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SystemOrdinaryTensorReduction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.Paper.SystemTensorMateArrows | R3 | Same statement and data; no adaptation required. |
| Sheaf.Paper.SystemTensorReductionFormula | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.RingTheory.AlgebraicRelativeDualizingIsomorphism | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.BoundaryAlphaNormalization | C6 | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.ClosedCostalkDuality | V4 | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.CompletedTensorShiftRight | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.EtaleGenericHomTriangle | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.EtaleHomThickLocus | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.EtaleOpenKFlat | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.EtaleOpenScalarCoherence | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.EtaleOpenTensor | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.EtaleOpenTensorDefs | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedDerivedAdjointLift | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedDerivedComparisonData | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedDerivedCompositionComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedDerivedIdentityComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedDerivedMonoidalComparisons | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedDerivedTensorDiagrams | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedDerivedTensorLift | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedDerivedTwoIsoComparison | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChange | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeCoordinates | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeData | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeHom | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.RingedFiniteFreeHomBaseChangeTensor | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.SixFunctors.SemilinearProperOpenMatePasting | C8 | Same statement and data; no adaptation required. |
| Sheaf.TraceFormula.AlgebraicShriekCalculus | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.TraceFormula.AlgebraicShriekRelativePerfect | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.TraceFormula.BigSmallEtaleLocalizationDerivedPushforward | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.TraceFormula.DerivedBasisLocalExtSheaf | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.TraceFormula.PolynomialDiagonalRhomReduction | unclaimed | Same statement and data; no adaptation required. |
| Sheaf.TraceFormula.UpperShriekBoundedCoherent | unclaimed | Same statement and data; no adaptation required. |

## Status

landed 20261020T235638-L-1200038 2026-10-20 (merge of deliver/Z6/Sheaf.CategoryTheory.RingedSiteDualityMaps)
