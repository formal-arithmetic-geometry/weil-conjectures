# finiteU_quotient_transition model import

## Reason

The module's public theorem directly uses finite dualizing model declarations.
The scalar reduction exchange module previously re-exported those declarations,
but the current rework build reports that import as bad while its model chain is
being repaired. Keep the model API explicit in this module's public imports.

## Old

```lean
public import Sheaf.SixFunctors.CoefScalarReductionExchange
```

## New

```lean
public import Sheaf.SixFunctors.CoefScalarReductionExchange
public import Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence | unclaimed | Receives the same declarations and theorem statement; no source adaptation is required. |

## Status

landed 20261027T180750-L-3898590 2026-10-27 (merge of deliver/Q8/Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient)
