# Names for the coefficient tensor normalization predicates

## Reason

The original ordinary existence-and-uniqueness statement repeats its full dependent
representative square directly in the predicate of ExistsUnique. The definitions
that select its uniquely determined comparison repeatedly check that large predicate.
A profiled compile identified 8.34 s plus 6.33 s around ordinaryComparison, in addition
to 26.6 s for the proof of ordinary_existsUnique. Name exactly the existing predicate
and use it in the theorem. No hypothesis, endpoint, comparison map or normalization
clause changes; unfolding ordinaryNormalization gives the old statement verbatim.
This is a definitionally identical presentation, not a weaker theorem or a different
choice of tensor comparison. Every old construction body, including
ordinaryComparison's choice from the uniqueness theorem, stays unchanged.
The proof also shares the existing coefficient-factor isomorphism in a typed local
binding, avoiding repeated conversion between its definitionally identical endpoints.

The added naturality and cancellation helpers are private, proved, and used only
in theorem proofs. The normalization cancellation and construction of the natural
isomorphism occur generically before specialization. The final transport and
composition of invertible completion maps are likewise performed in a generic
private lemma, preserving the existing completion argument and removing its old
local transparency override. A proved generic logical helper first forgets the
unused chain and augmentation data in the completion existence statement. This
reduces the dependent elimination motive while retaining the same witnesses and
complete-object property. The ordinary comparison definition is moved after the independent
completion theorem; its type and value are unchanged. Profiling commands are
removed from the submitted source. There are no new holes. No adopted source-library file changes.

## Old

```lean
theorem ordinary_existsUnique
    (T : ProEtaleTensorModel X (completedIntegralCommRingSheafUnrestricted l E X)) :
    ∃! e : T.tensor ⋙ integralDetailedTransport X l E ≅
        ((integralDetailedTransport X l E).prod (integralDetailedTransport X l E)) ⋙
          wfOrdinaryDerivedTensor X (pbcIntegralDatum l E),
      ∀ P Q : (proEtaleFlatRepresentatives X
        (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory,
        (integralDetailedTransport X l E).map (T.representative.hom.app (P, Q)) ≫
          e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)).map
            (Prod.mkHom
              ((fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app P.obj)
              ((fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (wfTensorModel X (pbcIntegralDatum l E)).representative.inv.app
            (⟨(complexTransport l E X).obj P.obj, good l E X P⟩,
              ⟨(complexTransport l E X).obj Q.obj, good l E X Q⟩) =
        (fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app
            ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map ((totalIso l E X P.obj Q.obj).hom) := by
  sorry
```

## New

```lean
def ordinaryNormalization
    (T : ProEtaleTensorModel X (completedIntegralCommRingSheafUnrestricted l E X))
    (e : T.tensor ⋙ integralDetailedTransport X l E ≅
      ((integralDetailedTransport X l E).prod (integralDetailedTransport X l E)) ⋙
        wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)) : Prop :=
  ∀ P Q : (proEtaleFlatRepresentatives X
        (completedIntegralCommRingSheafUnrestricted l E X)).FullSubcategory,
        (integralDetailedTransport X l E).map (T.representative.hom.app (P, Q)) ≫
          e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
          (wfOrdinaryDerivedTensor X (pbcIntegralDatum l E)).map
            (Prod.mkHom
              ((fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app P.obj)
              ((fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app Q.obj)) ≫
          (wfTensorModel X (pbcIntegralDatum l E)).representative.inv.app
            (⟨(complexTransport l E X).obj P.obj, good l E X P⟩,
              ⟨(complexTransport l E X).obj Q.obj, good l E X Q⟩) =
        (fdCoefficientTransport l E X).mapDerivedCategoryFactors.hom.app
            ((constructibleTensorTotal l E X).obj (P.obj, Q.obj)) ≫
          DerivedCategory.Q.map ((totalIso l E X P.obj Q.obj).hom)

/-- Ordinary coefficient transport is fixed by the signed-total representative square.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: compose the specified representative comparisons with total, and with the
exact transport factorization. The good theorem supplies the target resolving
objects. Double K-flat localization extends this square uniquely to a natural
isomorphism. Its inverse is obtained from the inverse total comparison. -/
theorem ordinary_existsUnique
    (T : ProEtaleTensorModel X (completedIntegralCommRingSheafUnrestricted l E X)) :
    ∃! e : T.tensor ⋙ integralDetailedTransport X l E ≅
        ((integralDetailedTransport X l E).prod (integralDetailedTransport X l E)) ⋙
          wfOrdinaryDerivedTensor X (pbcIntegralDatum l E),
      ordinaryNormalization l E X T e := by
  -- Proof by the existing representative-descent theorem and cancellation.
```

## Rational predicate: reason and exact old/new declarations

The final rational comparison selection has the same repeated-predicate cost
(6--8 s in profiled checks). Name its existing integral-representative predicate
as rationalNormalization, preserving the R and hR binders of the existence theorem.
Unfolding the predicate gives the original statement verbatim; its existing hole
is retained and is not counted as closed. The comparison choice body is unchanged.

Old:

```lean
theorem rational_existsUnique
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (hR : R.Normalized D C T₀ E₀) :
    ∃! e : rationalTensor D C T₀ E₀ ⋙ rational D C T₀ E₀ F W ≅
        ((rational D C T₀ E₀ F W).prod (rational D C T₀ E₀ F W)) ⋙ R.ordinary,
      ∀ M N : sfIntegralConstructibleCategory C.l
        (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left,
        HEq (e.hom.app
          ((sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
            (D.geometricFiber T₀).left).obj M,
            (sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
              (D.geometricFiber T₀).left).obj N))
          ((pbcStageLocalization C.l C.Qbar (D.geometricFiber T₀).left E₀).map
            (integralComparison D C T₀ E₀ F W M N).hom) := by
  sorry
```

New:

```lean
def rationalNormalization
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (e : rationalTensor D C T₀ E₀ ⋙ rational D C T₀ E₀ F W ≅
      ((rational D C T₀ E₀ F W).prod (rational D C T₀ E₀ F W)) ⋙ R.ordinary) : Prop :=
  ∀ M N : sfIntegralConstructibleCategory C.l
        (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left,
        HEq (e.hom.app
          ((sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
            (D.geometricFiber T₀).left).obj M,
            (sfRationalConstructibleLocalization C.l (pbcFiniteField C.l C.Qbar E₀)
              (D.geometricFiber T₀).left).obj N))
          ((pbcStageLocalization C.l C.Qbar (D.geometricFiber T₀).left E₀).map
            (integralComparison D C T₀ E₀ F W M N).hom)

attribute [local irreducible] rationalNormalization

/-- Rational tensor compatibility retains the canonical integral comparison on
every unchanged integral representative. Bilinearity fixes every denominator.
Source: step 13 (blueprint: def-sf-projection-tensor-coefficient-comparison).
Proof: localize integralComparison and its inverse. The integral_identity,
objects and tensors fields of the coefficient comparison identify the localized
endpoints and maps. The normalization of R.ordinary does the same for the tensor.
Naturality on integral maps extends by bilinearity to all localized maps.
All rational objects are unchanged integral representatives, giving uniqueness. -/
theorem rational_existsUnique
    (R : WfTensorCompletion.RationalComparison D C T₀ E₀)
    (hR : R.Normalized D C T₀ E₀) :
    ∃! e : rationalTensor D C T₀ E₀ ⋙ rational D C T₀ E₀ F W ≅
        ((rational D C T₀ E₀ F W).prod (rational D C T₀ E₀ F W)) ⋙ R.ordinary,
      rationalNormalization D C T₀ E₀ F W R e := by
  sorry
```

## Users

`tools/downstream.py Sheaf.Paper.ProjectionTensorCoefficientComparison --uses
ordinary_existsUnique` reports 107 downstream modules and only this module as a
textual user of ordinary_existsUnique. Repeating the check with
rational_existsUnique also finds only this module (the same 107 downstream modules). None needs adaptation: the new predicate is
definitionally the exact old predicate. The signatures and bodies of the exported
comparison constructions remain unchanged. No target or the meaning of a definition
used by a target changes. All modules below are unchanged; no adaptation of another
group's work is submitted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionTensorCoefficientComparison | J8 | The theorem uses a name for its identical old predicate; choice bodies unchanged. |
| Sheaf.Paper.AdicCompletedProjectionShift | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicNormalizedPurityLift | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicProjectionShiftCoherence | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicProjectionShiftData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicPurityScalarNaturality | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicTraceTensorShift | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicTraceTransposeData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicUnitTraceConstruction | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicUnitTraceReductionData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicUnitTraceScalarData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AffineSpaceLastFactorProduct | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AffineSpaceProductDomain | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AffineSpaceTraceContractionProduct | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AffineSpaceTraceFactorization | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AffineSpaceTraceProductData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.AffineSpaceTraceSuccessorContraction | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.CoefficientGammaRepresentatives | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.CompactSupportProjectionFormula | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.CompactificationCompletedRealization | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.CompactifiedTowerComparisons | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.FiniteReductionOfPurity | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.FrameworkPbcComparisonData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.FrameworkPbcComparisonSystem | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.FrameworkPbcIntegralComparisonLaws | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.FrameworkPbcPullbackScalarBridge | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.FrameworkPbcRawComparisonData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.FrameworkPbcRawComparisonLaws | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.HomChainPairingNaturality | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.IntegralPurityComparisonCocycles | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.IntegralPurityCounitReduction | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.IteratedPurityScalarPasting | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.NormalizedFieldPurityTrace | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.NormalizedFieldPurityTraceCommonStage | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.PodCtfAdjunctions | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.PodCtfPairingMaps | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.PodHomChainCounitFormula | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.PodHomChainCtfDomains | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.PodHomChainUncurriedTransport | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.ProjectionFormulaCoherence | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.PurAdicReconstruction | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.PurityTensorMapNaturality | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RationalExceptionalFinalEquations | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RationalPurityComparisonDescent | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RationalPurityScalarLocalization | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RationalPuritySourceLocalization | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RationalScalarComparisonData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RelativeKunneth | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RelativeKunnethCubeFactorTransport | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.RelativeProductBaseChangeFactorSquares | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.SfCoefficientComparisonConclusions | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.SmoothOperationCoefficientModels | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.SmoothOperationDescentSpecification | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.SmoothPurityFieldExtension | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TensorHomCoefficientTransposes | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TensorHomExchange | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TensorMapPresentationIndependent | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TensorMateInvertibleInput | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TowerPurityRealizedData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TowerPurityRealizedNormalization | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TowerPurityRealizedTranspose | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackSquareScalars | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.VerdierHomChainComposition | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.VerdierHomChainCompositionData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.VerdierIdentityProjection | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.VerdierOrdinaryTensorTransport | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.VerdierProjectionExceptionalPaste | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.WeilChosenDualityExchange | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.WeilChosenDualityExchangeData | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.WeilChosenExchangeConstruction | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.Paper.WeilChosenTransposeNaturality | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.SixFunctors.CompactifiedProperTowerExchange | not adapted | Identical public construction types and bodies; no source edit. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted | Identical public construction types and bodies; no source edit. |

## Status

landed 20261026T070117-L-3389104 2026-10-26 (merge of deliver/J8/Sheaf.Paper.ProjectionTensorCoefficientComparison)
