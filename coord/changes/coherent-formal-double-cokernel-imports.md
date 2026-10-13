# coherentFormalModule_annihilated_double_cokernel

## Reason

The completed cokernel-only proof does not use List.TFAE. Remove its public import
while retaining the theorem's exact signature and all declaration visibility.
All new imports serve only proofs. No definition or statement changes.

## Old

```lean
public import Mathlib.Data.List.TFAE
```

## New

The unused public List.TFAE import is removed. The other public imports remain.
The existing theorem signature and its meaning are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleCokernel | D4 | proof closed; unused public import removed |
| Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated | not queried; no adaptation | sole direct importer, already publicly imports Mathlib.Data.List.TFAE itself |

The sole direct importer imports this item for its proof, rather than publicly.
It already has its own public List.TFAE import. Thus its public API and all
transitive users are unaffected. No adaptation or target statement review is needed.
Its original file is compiled separately against the delivered module overlay.

## Status

landed 20261013T003155-L-2428349 2026-10-13 (merge of deliver/D4/Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilatedDoubleCokernel)
