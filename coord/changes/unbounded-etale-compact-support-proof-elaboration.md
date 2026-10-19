# UnboundedEtaleCompactSupportComparisons proof elaboration commands

## Reason

The proof adds proof-only imports and a local irreducibility attribute so that
the mate transport and identity cancellation proofs elaborate without unfolding
the exchange definition. The attribute is local to this module and does not alter
any exported declaration or statement.

## Old

The module had the original proof-only import list and no local irreducibility
attribute for `unboundedEtaleCompactSupportBaseChange`.

## New

The module imports `UpperLowerStarAdjunctionCompat`, `MapDerivedCategoryMate`,
and `UpperLowerStar.Coherence` for the private mate lemmas, and contains:

```lean
attribute [local irreducible] unboundedEtaleCompactSupportBaseChange
```

The attribute is scoped to this file and is used only while proving the identity
base-change theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons | Y8 | Local proof elaboration only. |
| Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate | unclaimed | Unchanged exchange definition and signature. |
| Sheaf.AlgebraicGeometry.EtaleShriekOpenExchangeAdjoint | B6 | Unchanged exchange definition and signature. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Unchanged compactification exchange. |

`tools/downstream.py --uses` found the three consumers above. None requires an
adaptation: all definition bodies, signatures and exported attributes are unchanged.

## Status

landed 20261019T034403-L-427919 2026-10-19 (merge of deliver/Y8/Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons)
