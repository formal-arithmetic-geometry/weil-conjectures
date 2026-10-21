# Sheaf.Paper.RelativeSupportBottomDescent

## Reason

Restore the assigned quarantined module from the archive recorded in coord/rework.tsv.
The archive still imports the retired forwarding module for scalar forgetting. Migrate
that import to its canonical upstream owner and fill the canonical interface proofs.
All 36 public declaration headers, all public definition bodies, and all instance
attributes are unchanged. No target statement or mathematical definition changes.

## Old

The archived module's public scalar-comparison import was:

```lean
public import Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
```

The module was absent from lean/ and preserved at
quarantine/Sheaf/Paper/RelativeSupportBottomDescent.lean, with 16 named theorem holes.

## New

```lean
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
```

The canonical owner publicly imports the coefficient-comparison API as well. Its
existing private evaluation-acyclicity theorem is accessed with a separate import all.
The module is restored at lean/Sheaf/Paper/RelativeSupportBottomDescent.lean. Fifteen
original theorem holes are proved, with one original final theorem hole retained.
Only proved private helpers are added. No source-library file is changed.
The direct private SupportLongExact import is removed: the supported site-comparison
proof now uses derived comparison direct image and its unit. That module remains
transitively imported by the public SupportSiteComparison interface.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RelativeSupportBottomDescent | W5 | Restore and prove its canonical interfaces; signatures and definitions preserved. |
| Sheaf.Paper.PurityFrameIndependence | unclaimed, quarantined | Existing import and final-theorem dependency preserved; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed, quarantined | Existing import and bottom-descent dependency preserved; no adaptation. |

The live downstream index reports the assigned module absent, as expected for this
quarantine repair. The consumer list above comes from an explicit search of both lean/
and quarantine/. Both archived consumers are retained and neither needs an interface
adaptation. No target-meaning review is reopened because no definition changes.

## Status

landed 20261021T194508-L-1727104 2026-10-21 (merge of deliver/W5/Sheaf.Paper.RelativeSupportBottomDescent)
