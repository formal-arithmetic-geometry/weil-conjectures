# WeilConjectures.ScalarExtensionTower.scalarPullbackRoosCoordinate

## Reason

Expose the strict quotient coordinate and two one-sided normalization obligations that the
assigned mate equation needs. All existing public signatures and imports are preserved; the
only existing module changed is the assigned item, and its changes are proof-only.

## Old

No declarations in the three new modules existed. The assigned declaration's signature is
unchanged and is recorded verbatim by its existing DAG node.

## New

New declarations in `Sheaf.Paper.ScalarPullbackRoosCoordinates`:
`ScalarPullbackQuotientFormula`, `scalarPullbackRoosCoordinate`, `scalarPullbackRoosChain`,
`scalarPullbackRoosCoordinates_exists`, `scalarPullbackQuotient_computes`, all in namespace
`WeilConjectures.ScalarExtensionTower`. The first three have explicit definition bodies; the
last is proved. The coordinate node records their names and the exact existence signature.

New independent normalization statements `scalarPullbackLeftRoos` and `scalarPullbackRightRoos`
in the corresponding new modules, with exact signatures in their new nodes.
No existing definition, statement, instance or attribute is changed.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ScalarTowerPullbackLimitBridge | R3 | complete proof from the new normalization declarations |
| Sheaf.Paper.ScalarPullbackLeftRoos | R3 (new) | left route stated using explicit coordinates |
| Sheaf.Paper.ScalarPullbackRightRoos | R3 (new) | right route stated using explicit coordinates |

No published module could mention these new names. No existing consumer requires adaptation.

## Status

landed 20261027T234253-L-83762 2026-10-27 (merge of deliver/R3/Sheaf.Paper.ScalarTowerPullbackLimitBridge)
