# Ordinary scalar model definition extraction

## Reason

The item proof is split into a rank-one comparison and its finite-presentation
extension.  Those new theorem modules must use the ordinary source, target and
compositor definitions without importing the item module back into itself.  The
already proved definitions and exactness lemmas are therefore moved to a base
module; the public names and all declaration signatures stay unchanged.

## Old

`Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModel` contained the ordinary source,
target, exactness, and compositor declarations together with the final theorem.
The proof-only imports were `Sheaf.Paper.FinitePerfectAdicConstantCohomology`,
`Sheaf.Paper.CompletedKoszulFiniteQuotientComparison`, and
`Sheaf.Paper.CompletedConstantAlgebraFlatQuotients`.

## New

`Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModelBase` contains those existing
ordinary definitions, exactness lemmas, and compositor declarations.  The item
module publicly imports the base and contains the unchanged final theorem
statement, proved from the two split theorem modules.  The declarations retain
their names, namespaces, types, attributes, and behavior.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.FinitePerfectAdicScalarModelFactors` | unclaimed | imports the item module and continues to receive all ordinary declarations through its public base import |
| `Sheaf.Paper.FinitePerfectAdicScalarModel` | unclaimed | receives the ordinary declarations from the base module and uses the split comparison theorems |

## Status

landed 20261028T035029-L-3582625 2026-10-28 (merge of deliver/Z8/Sheaf.Paper.FinitePerfectAdicOrdinaryScalarModel)
