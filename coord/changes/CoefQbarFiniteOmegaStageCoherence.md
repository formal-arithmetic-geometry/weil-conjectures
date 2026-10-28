# CoefQbarFiniteOmegaStageCoherence interface

## Reason

The proof is decomposed into two new finite tower statements and imports those proof
modules. The item's public theorem statement is unchanged.

## Old

The item imported only `Sheaf.SixFunctors.CoefQbarVerdierData` and contained the
`finiteOmegaStageComparison_tower` theorem with a `sorry` proof.

## New

The item imports the two proof modules
`Sheaf.SixFunctors.CoefQbarFiniteOmegaTransitionTower` and
`Sheaf.SixFunctors.CoefQbarOperationStageTransitionTower`; its public theorem statement
is unchanged and its proof uses a private categorical transport lemma.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.CoefQbarVerdierEvaluationDescent | U4 | compiles against the unchanged theorem statement |

## Status

landed 20261028T020759-L-2547717 2026-10-28 (merge of deliver/T4/Sheaf.SixFunctors.CoefQbarFiniteOmegaStageCoherence)
