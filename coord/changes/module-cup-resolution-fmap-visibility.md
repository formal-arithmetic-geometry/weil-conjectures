# AlgebraicGeometry.Scheme.Modules.cupResolution_class_fmap

## Reason

Restore the quarantined item from its rework archive and make the definition used in its
public theorem signature publicly visible. The quarantine compiler error was:
`Unknown identifier moduleCohomologyFMap`; the defining module was imported privately.
The theorem signature and the two existing public definitions are unchanged.

## Old

```lean
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
```

## Users

The live source has no importers because the item and its parents are quarantined.
Searching both live roots and both quarantine roots finds these consumers:

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupResolutionFMap | M1 | Public signature can name its defining cohomology map. |
| Sheaf.Paper.ModuleCupPullbackAugmentedPairings | unclaimed | Publicly imports the item; gains the definition needed by the item signature. |
| Sheaf.Paper.ModuleCupPullbackResolutionMaps | unclaimed | Uses all three existing declarations through the preceding module; signatures and bodies remain compatible. |

Both unchanged quarantined consumer modules compiled against the restored item with
`lcompile.py --all`; the item also compiled without warnings in 30.3 seconds.
No consumer adaptation is needed. The existing statements, definitions and universes stay
identical. No target statement or definition changes.

## Status

landed 20261020T145524-L-2406615 2026-10-20 (merge of deliver/M1/Sheaf.Paper.ModuleCupResolutionFMap)
