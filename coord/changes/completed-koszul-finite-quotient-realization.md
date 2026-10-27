# completedKoszulFiniteQuotientRealization

## Reason

The target proof introduces two helper modules and local monoidal instances to isolate the exactness and finite quotient comparison steps.

## Old

The target module declared local tensor instances and contained one bundled proof hole.

## New

The target combines `completedKoszulFiniteQuotientExactness` and `completedKoszulFiniteQuotientComparison`; helper declarations are proof-only dependencies.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CompletedKoszulFiniteQuotientRealization | S3 | target proof uses the split lemmas |
| Sheaf.Paper.CompletedKoszulFiniteQuotientComparison | S3 | new helper module |
| Sheaf.Paper.CompletedKoszulFiniteQuotientExactness | S3 | new helper module |

## Status

landed 20261027T050643-L-249600 2026-10-27 (merge of deliver/S3/Sheaf.Paper.CompletedKoszulFiniteQuotientRealization)
