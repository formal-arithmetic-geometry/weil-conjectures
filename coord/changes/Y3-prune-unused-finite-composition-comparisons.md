# finiteReductionOfCompositionSource and finiteReductionOfCompositionExceptional

## Reason

Prune two unused auxiliary statements under Sheaf. The latest blueprint theorem
requires reduction of the actual purity-composition path; that clause is exactly
finiteReductionOfCompositionCoherence and has a direct proof. Specialize the main
finiteReductionOfPurity square to f ≫ g and rewrite both purity maps by
smoothPurityCompositionCoherence. This retains the original source identification,
the two original purity arrows and the original exceptional composition isomorphism.
No separate reduction identity of either outer isomorphism is needed.

Both downstream.py --uses scans find only the owning declaration itself. A global
source/DAG search finds these names only in their definitions and the owning node's
Lean attachment. All actual DAG parents were read by dependency edges, including
parents whose Lean attachment is absent. They use the retained main purity square,
orientation, traces, or full composition/base-change clauses. None requires the
separate stronger source- or exceptional-compositor equation. The unit
sk-thm-purity-transport Step 1 and its realized route are unchanged. Challenge.lean
contains neither retired name. No adopted WeilConjectures declaration is edited.

## Old

```lean
theorem finiteReductionOfCompositionSource (K : Scheme.proEtaleDerivedCategory Z P.Ring) :
    (P.finiteReduction m hm hmn X).map
        (P.compositionSourceIdentification f g d e K).hom ≫
      (P.finiteReductionSourceComparison m hm hmn f d
        ((P.compositionShiftedPullback g e).obj K)).hom ≫
      (((P.finiteReductionSetting m hm).compositionShiftedPullback f d).map
        (P.finiteReductionSourceComparison m hm hmn g e K).hom) =
    (P.finiteReductionSourceComparison m hm hmn (f ≫ g) (d + e) K).hom ≫
      ((P.finiteReductionSetting m hm).compositionSourceIdentification f g d e
        ((P.finiteReduction m hm hmn Z).obj K)).hom

theorem finiteReductionOfCompositionExceptional
    (K : Scheme.proEtaleDerivedCategory Z P.Ring)
    (hK : finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Z K) :
    (P.finiteReduction m hm hmn X).map (P.compositionExceptionalIso f g K hK).hom ≫
      P.finiteReductionExceptionalComparison m hm hmn f d
        ((P.compositionExceptional g).obj K) (P.compositionExceptional_ctf g e K hK) ≫
      ((P.finiteReductionSetting m hm).compositionExceptional f).map
        (P.finiteReductionExceptionalComparison m hm hmn g e K hK) =
    P.finiteReductionExceptionalComparison m hm hmn (f ≫ g) (d + e) K hK ≫
      ((P.finiteReductionSetting m hm).compositionExceptionalIso f g
        ((P.finiteReduction m hm hmn Z).obj K)
        (P.finiteReduction_preserves_ctf m hm hmn Z K hK)).hom

```

## New

The two unused auxiliary declarations are withdrawn. Their full blueprint clause
remains as finiteReductionOfCompositionCoherence, with its exact original signature
and specified comparison arrows. Its complete Lean proof is:

```lean
  have h := P.finiteReductionOfPurity m hm hmn (f ≫ g) (d + e) K hK
  rw [P.smoothPurityCompositionCoherence f g d e K hK,
    (P.finiteReductionSetting m hm).smoothPurityCompositionCoherence f g d e] at h
  exact h
```

The owning node's Lean declaration list and proof plan now name just the six retained
blueprint clauses. No definition, existing retained signature or public import changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteReductionOfPurity | Y3 | Remove only the two unused auxiliary declarations; retain the complete direct composition proof. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicNormalizedPurityLift | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicPurityScalarNaturality | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicUnitTraceConstruction | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicUnitTraceReductionData | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicUnitTraceScalarData | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.CommonStageSmoothOperationIdentification | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.PurAdicReconstruction | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.RationalExceptionalFinalEquations | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.RationalPurityCoherenceDescent | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.RationalPurityComparisonDescent | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.RationalPurityScalarLocalization | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.RationalPuritySourceLocalization | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.RationalScalarComparisonData | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.RationalScalarComparisonIdentification | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.SmoothOperationCoefficientComparisons | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.SmoothOperationCoefficientModels | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.SmoothOperationDescentSpecification | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.SmoothOperationIdentificationSpecification | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.SmoothPurityFieldExtension | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackAdicIdentification | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackCoefficientCoherence | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackPbcPullback | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackPbcTwist | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackScalarPrimitives | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackScalarShifts | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackSquareMaps | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackSquareScalars | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not queried (unchanged) | Neither name occurs; no adaptation or semantic change. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | not queried (quarantined; unchanged) | Quarantine source imports this module but uses neither retired name; no adaptation. |

The first 45 downstream modules above are the entire downstream.py output for each name.
The quarantined sources were also searched directly: only
NormalizedOrientationPerfectDuality and the already listed LowerShriekFunctoriality
import this module, and neither uses either retired declaration.
Neither name has a caller, so there are no forced adaptations or target reviews to
reopen: all definitions and the target-relevant theorem signatures are unchanged.

## Status

landed 20261025T212758-L-232091 2026-10-25 (merge of deliver/Y3/Sheaf.Paper.FiniteReductionOfPurity)
