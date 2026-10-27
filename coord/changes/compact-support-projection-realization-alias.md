# WeilConjectures.CompactSupportPbcTransport.realization

## Reason

The coefficient comparison and its cancellation used separately expanded copies of
the same coefficient functor, causing expensive kernel comparisons. Use the existing
named functor directly. The definition remains definitionally equal to its original
body: the target name unfolds to the identical three inherited facts and recorded
rational functor. Every statement and target retains its meaning.

## Old

```lean
def realization : sfRationalConstructibleCategory C.l
    (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left ⥤
      pbcStageCategory C.l C.Qbar (D.geometricFiber T₀).left E₀ :=
  letI := W.noetherian
  letI := W.dimension
  letI := W.invertible
  ((F.coefficients (D.geometricFiber T₀).left).stage E₀).rational.functor
```

## New

```lean
def realization : sfRationalConstructibleCategory C.l
    (pbcFiniteField C.l C.Qbar E₀) (D.geometricFiber T₀).left ⥤
      pbcStageCategory C.l C.Qbar (D.geometricFiber T₀).left E₀ :=
  CompactSupportCoefficientTensor.rational D C T₀ E₀ F W
```

## Users

The downstream name search returned these six modules. All external hits were
inspected: they use other realization declarations, not this transport functor.
There are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unclaimed | Textual name match only; uses a different realization declaration. |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Textual name match only; uses a different realization declaration. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Textual name match only; uses a different realization declaration. |
| Sheaf.Paper.CompactSupportProjectionFormula | F4 | Alias definition; existing uses are definitionally unchanged. |
| Sheaf.Paper.ProjectionFormulaCoherence | V5 | Textual name match only; uses a different realization declaration. |
| Sheaf.Paper.TensorHomExchange | unclaimed | Textual name match only; uses a different realization declaration. |

## Status

landed 20261025T201914-L-2644369 2026-10-25 (merge of deliver/F4/Sheaf.Paper.CompactSupportProjectionFormula)
