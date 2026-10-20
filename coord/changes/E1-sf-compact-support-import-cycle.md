# SfIntegralCompactSupportConstructible: remove the cycle-closing proof import

## Reason

The proved integral adjunction uses SystemOperationExchangeRealization. Its compact-support
import closure reaches SfIntegralCompactSupportConstructible, which unnecessarily imported
the assigned module. This closes an import cycle when the assigned module imports the
proved integral adjunction. SfIntegralCompactSupportConstructible mentions none of the
assigned module's declarations and compiles after removing just that ordinary import.

The failed earlier route reported this cycle:

```
SfCommonStageDirectImage -> SfRationalDirectImageAdjunction ->
SystemOperationExchangeRealization -> QcqsCompactSupportRealization ->
CompactSupportFiniteAction -> CompactSupportRepresentativeIndependence ->
IntegralRationalQbarCompactSupport -> SfIntegralCompactSupportConstructible ->
SfCommonStageDirectImage
```

The current route inserts SfIntegralPullbackLinearAdjunction before the system module;
the same cycle-closing edge must be removed. The launcher's 2026-10-19 import-only
adaptation exception requires independent review of this necessity; the unchanged file
would compile alone, but the combined import graph would be cyclic.

## Old

```lean
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.Paper.SfCommonStageDirectImage
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
```

## New

```lean
import Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
```

All other bytes of the adapted module agree with the current source. Public imports,
all declaration signatures and bodies, and visibility are unchanged. No definition or
target meaning changes. The adapted module compiled in 11.1 seconds. Its two original
named theorem holes are unchanged and are not new holes of this delivery.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfIntegralCompactSupportConstructible | K9 | Only the unused ordinary import is removed; no declarations change. |
| Sheaf.Paper.CompactSupportProjectionFormula | A4 | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.CompactSupportRepresentativeIndependence | R9 | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.CompactSupportSystemRealizationNormalization | unclaimed | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.DirectImagesConstructible | G1 | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.FieldShriekCompositionQcqs | S6 | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.FieldShriekLowerBound | F1 | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.FrobeniusExchangeEquivalence | V9 | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.ImmersionWeilLocalBehavior | unclaimed | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientComparison | X2 | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.IntegralCompactSupportCoefficientData | W7 | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.IntegralRationalQbarCompactSupport | unclaimed | Same public imports and declarations; no adaptation. |
| Sheaf.Paper.ZlImmersionWeilLocalBehavior | U2 | Same public imports and declarations; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same public imports and declarations; no adaptation. |

These are the direct importers from tools/downstream.py --direct. Removing an ordinary
proof import changes no exported interface, so transitive consumers see the same API.
The independent reader and global build check the complete import closure.

## Status

landed 20261020T051204-L-1589890 2026-10-20 (merge of deliver/E1/Sheaf.Paper.SfCommonStageDirectImage)
