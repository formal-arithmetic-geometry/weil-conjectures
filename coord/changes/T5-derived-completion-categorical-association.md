# AlgebraicGeometry.ProEtale.AdicCompletion.reductionComp

## Reason

Factor the purely categorical association of adjunctions before specializing to continuous
coefficient objects. Profiling showed repeated synthesis of the pulled-back monoidal ring
structures and complex products. Named local instances cache precisely the existing instances;
the local irreducibility attribute prevents expansion of the continuous inverse-image
construction during proof search. The local attributes do not escape this file. They are reapplied at each namespace
boundary, including the namespace containing `IsDerivedComplete`, so this definition
uses the same cached instances as the Roos construction.

The new `adjunctionAssociation` is exactly the old composition expression. All existing public
signatures and all coefficient objects, maps, tensor levels, Roos coordinates, augmentation and
normalization constructions retain their meanings. No target changes. The theorem `roosD_sq`
uses a proved generic square-zero calculation. Generic private helpers are used only by proofs.
The explicit `transition_isMonHom` proves the already available canonical morphism property.

## Old

```lean
def reductionComp (n : ℕ) :
    derivedReduction l E X (n + 1) ⋙ finiteExtend l E X n ≅ derivedReduction l E X n :=
  (((Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1))).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n))).ofNatIsoRight
        (restrictComp l E X n)).leftAdjointUniq
    (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n))
```

## New

```lean
def reductionComp (n : ℕ) :
    derivedReduction l E X (n + 1) ⋙ finiteExtend l E X n ≅ derivedReduction l E X n :=
  let a : derivedReduction l E X (n + 1) ⊣ restrict l E X (n + 1) :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X (n + 1))
  let b : finiteExtend l E X n ⊣ finiteRestrict l E X n :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (transition l E X n)
  let c : derivedReduction l E X n ⊣ restrict l E X n :=
    Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)
  adjunctionAssociation a b c (restrictComp l E X n)
```

`adjunctionAssociation a b c e` is defined as
`((a.comp b).ofNatIsoRight e).leftAdjointUniq c`. Thus the two definitions are
judgmentally equal. Existing data definitions otherwise keep their original written bodies,
with cached, definitionally identical instance constants.

## Users

The following is the transitive importer list from `tools/downstream.py` with its `--uses
reductionComp` query. Its direct-use filter reports only the item and
`SmallCoefficientDerivedCompletion`; the latter expands the same association expression.
No consumer is changed in this packet. The unchanged
`SmallCoefficientDerivedCompletion` compiles against the delivered modules through
`lcompile.py` (sandbox log `consumer-real-root.log`).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IntegralConstantCompletion | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.AlgebraicGeometry.IntegralModelsStacks | W6 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.AlgebraicGeometry.ProperHeartBoundRational | J6 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsClosedPullbackFiniteModelCompletion | V4 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.AlgebraicGeometry.QcqsProperOpenBoundaryVanishing | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.AdicLisseCohomologyCalculus | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.AdicQbarConstructibleRealization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.BrownHypothesesGeneration | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.CompactificationCompletedRealization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.CompleteIntegralResidueFunctor | T2 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.CompleteResidueLineInverse | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.CompletionTriangleComparison | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.ConstructibleCompactness | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.ConstructibleProjectiveChartRefinement | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DerivedNakayama | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientCategory | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientDiagrams | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientEndpoints | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientExchange | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFamilyPullback | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteDiagonal | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientFiniteRealization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientMaps | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullback | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientPullbackEndpoints | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotientLine | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientQuotients | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientReference | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientScalars | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCoefficientSourcePullback | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCompletedBaseChange | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalCompletedRealization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalFamilyExtension | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalFiniteReductions | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalScalarBaseChange | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalTowerLimit | E6 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalTowerTrace | E7 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceCoefficients | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalTowerTraceModels | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.DiagonalTowerTracePresentations | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.FiniteEtaleAdicCohomology | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.FiniteModelSheafQuotientConstructible | X7 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.FiniteScalarLocalModelComplete | X9 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.FiniteStrataCompletionDetection | Y6 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.FiniteWindow | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.FiniteWindowBounded | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.FiniteWindowUnbounded | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.FourierArtinSchreierProperties | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.GeneralLfpAdicInputWitness | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralAdicHomCompleteness | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralAdicHomResidueOrigin | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralAdicInputNormalization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralAmbientTowerComparison | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralCoefficientModelRealization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralCohomologicalAdicCriterion | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralConstantModelHeart | Z8 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralConstructibleCompletionBridge | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralConstructibleExt | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralConstructibleHeart | F5 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | C9 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralGeneralLfpHomFiniteness | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralHeartDualizable | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralHeartLocalModel | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralHeartRealizationExact | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralHeartResidueDual | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralModels | J8 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralModelsOperations | V1 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralProperReductionBound | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralProperReductionModel | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralQuotientResolutionNormalization | H2 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralResidueClassTriangleClosure | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralSectionLocalModels | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralStratumExtBound | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralTensorProduct | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.IntegralTensorPullback | H4 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.NativeAdicFiniteNormalization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.NativeAdicRealizationData | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.NativeAdicReindexingData | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.NativeAdicTensorReindexing | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.PrincipalReductionConeCalculus | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.PrincipalReductionDerivedNormalization | Q8 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.ProjectiveDiagonalPullback | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.ProperHeartBoundLattice | G8 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.QcqsIntegralFiniteModelCompleteness | H8 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.QcqsProperConstructibleClosedBaseChange | N1 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.RationalLocalizedHom | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.RationalRealizationTensorComparison | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.RationalTatePullback | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.ResidueLisseProjectiveModels | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.StrictCompletionRestrictionComparison | F2 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.SuccessiveReductionConstructibility | F8 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.SystemRefinementConstructibleDomain | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.TateTwistLisseLine | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.UniformConstructibleExt | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtIntegral | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtRational | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.AmbientClopenRestrictionUniqueness | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ConstructibleTensorCompletion | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralBasicRealization | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralSystemCanonicalBridge | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.IntegralTensorInverseImage | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenFactorCoherence | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenFactorPullModel | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenFactorTensorModel | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenProjectionRoosCompletion | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralCompletionPresentation | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares | M5 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralPresentationEncoding | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralReductionTransitionComparison | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion | unclaimed | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion | unclaimed | Same canonical association after unfolding adjunctionAssociation; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypotheses | Q3 | Definitionally identical constructions and signatures; no adaptation. |
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteFieldCompactness | unclaimed | Definitionally identical constructions and signatures; no adaptation. |

## Status

landed 20261024T020553-L-2620352 2026-10-24 (merge of deliver/T5/Sheaf.SixFunctors.ProEtale.DerivedCompletion)
