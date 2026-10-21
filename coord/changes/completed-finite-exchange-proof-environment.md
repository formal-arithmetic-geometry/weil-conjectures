# Completed finite exchange proof environment

## Reason

Preflight requests a change record for the added local attribute commands in
`Sheaf.Paper.CompletedFiniteExchangeCoordinates`. These commands control
elaboration of the new private proofs, without changing a public signature or
public definition. The two continuity helpers are private proved theorems,
registered as instances only locally.

## Old

The module had no added local attributes on
`proEtaleRingModulePullback`, `proEtaleRingModuleAdjunction`, `finiteOpenRing`,
`finiteOpenAdjunction`, or `finiteSliceRing`, and no private open-slice
continuity helpers.

## New

```lean
attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
attribute [local irreducible] finiteOpenRing
attribute [local irreducible] finiteOpenAdjunction
attribute [local instance] openSliceContinuous openSliceCompContinuous
attribute [local irreducible] finiteSliceRing
```

All attributes above are local to this module. The first two declarations are
existing definitions; the others are new private, proved helpers. No public
statement, definition body, visibility, or public import is modified. The
irreducibility attributes prevent elaboration from unfolding large adjunction
and ring-comparison terms. Explicit helper lemmas provide the equations used by
the proofs. No target meaning changes and no consumer adaptation is required.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedFiniteExchangeCoordinates | K5 | Local proof elaboration only. |
| Sheaf.Paper.CompletedFiniteComparisonModels | Unclaimed in shared records | Public interface unchanged. |
| Sheaf.Paper.CompletedOpenFiniteEtaleOrigins | Unclaimed in shared records | Public interface unchanged. |

## Status

landed 20261021T214817-L-1859780 2026-10-21 (merge of deliver/K5/Sheaf.Paper.CompletedFiniteExchangeCoordinates)
