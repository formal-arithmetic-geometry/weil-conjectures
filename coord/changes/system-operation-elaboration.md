# SystemOperationExchangeRealization elaboration instances

## Reason

Overlapping sheafification instances cause elaboration of this module to exceed
its compile limit. Temporarily remove them during this file and restore them by closing a section at
its end. No definition or statement is changed. The delivered file compiles in
29.6 seconds. The static command-surface check requests this record because it
sees the attribute commands.

## Old

No instance-removal commands occurred in this module.

## New

After the existing options, open a section:

```lean
section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
```

After the closing namespace, close that section with `end`. This restores the
original instance attributes by Lean section scoping.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SystemOperationExchangeRealization | K1 | proofs only; instances restored at end |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | no adaptation; declarations unchanged |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | no adaptation; declarations unchanged |

## Status

landed 20261019T231224-L-562771 2026-10-19 (merge of deliver/K1/Sheaf.Paper.SystemOperationExchangeRealization)
