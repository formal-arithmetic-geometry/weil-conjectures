# AlgebraicGeometry.Scheme.Modules.exists_globalTensorPullback_underived_data

## Reason

Return C-03a5b (head 03a5bf890) explicitly requests restoring the quarantined
implementation with its K-flat public import switched to the adopted source
module. The archived Sheaf K-flat module conflicts with the adopted source
K-flat declarations. The previous attempted upstream re-export also conflicted
with the Sheaf cup-map module imported by the parent. This repair follows the
reviewer's exact implementation correction; it does not substitute the upstream
cup map or monoidal normalization for the node's recorded Sheaf dependencies.

Preflight requires a change record for the public-import replacement. This
record replaces no claims of the rejected
`global-tensor-pullback-underived-upstream.md`, which is removed from the packet.

## Old

In the quarantined item:

```lean
public import Sheaf.Algebra.Homology.KFlatPullback
```

The rejected packet instead had the sole public import:

```lean
public import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackUnderivedData
```

## New

The complete archived item is restored, with this one import replacement:

```lean
public import WeilConjectures.Algebra.Homology.KFlatPullback
```

The archived `Sheaf.Paper.ModuleCupNaiveMap` public import and
`Sheaf.Paper.GlobalTensorPullbackMonoidalNormalization` private proof import
are restored. All other archived imports, the complete theorem signature, and
the theorem proof are unchanged. Only six local instance declaration lines are
wrapped after their colons to satisfy the width limit. No definition or target
statement changes, and no adopted source-library module is edited.

The node is restored to `existing: false` and the item's own Sheaf module and
file. Its statement and dependencies are unchanged.

## Users

The item is absent from `lean/` because it is quarantined. A source search of
both `lean/Sheaf/` and `quarantine/Sheaf/` finds the single direct importer below.
There are no other occurrences calling its theorem in those trees except the
archived item itself. The parent destructures the same existential theorem at
line 181; its statement does not become weaker, stronger, or different.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.GlobalTensorPullbackUnderivedData | E1 | Assigned zero-hole repair; restores the complete archived theorem with corrected public K-flat import. |
| Sheaf.Paper.ModuleCupGlobalTensorPullback | unclaimed | Quarantined direct importer; theorem signature unchanged. The repaired item imports successfully together with its Sheaf cup-map dependency. The parent's separate obsolete K-flat import and derived-data rework are not repaired by this delivery. |

The simultaneous-import probe for `Sheaf.Paper.ModuleCupNaiveMap` and the
restored item compiles. The restored theorem's axioms are exactly `propext`,
`Classical.choice`, and `Quot.sound`. This establishes the requested item's
repair; it does not claim the separately quarantined parent compiles unchanged.

## Status

landed 20261020T160942-L-3429494 2026-10-20 (merge of deliver/E1/Sheaf.Paper.GlobalTensorPullbackUnderivedData)
