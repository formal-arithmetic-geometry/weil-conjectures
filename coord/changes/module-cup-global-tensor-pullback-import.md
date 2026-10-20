# Sheaf.Paper.ModuleCupGlobalTensorPullback public imports

## Reason

Restore the quarantined item listed in coord/rework.tsv. Its public theorem uses
CochainComplex.tensorPullbackRingMap, which is defined in the upstream module
WeilConjectures.Algebra.Homology.KFlatPullback. The former Sheaf import is now
an empty withdrawn module, so it no longer exposes this declaration. Private
proof imports do not make it available to public statements.

## Old

```lean
public import Sheaf.Algebra.Homology.KFlatPullback
```

## New

```lean
public import WeilConjectures.Algebra.Homology.KFlatPullback
```

All other source text is identical to the quarantine archive. Both public
signatures and the body of moduleCup_globalTensorDiagram are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ModuleCupGlobalTensorPullback | G1 | Restored from quarantine; explicit public import fixes its statement elaboration. |
| Sheaf.Paper.ModuleCupKInjectiveTarget | quarantined; holder not recorded locally | Same theorem and definition; no adaptation required. |
| Sheaf.Paper.ModuleCupGlobalTensorComparison | quarantined; holder not recorded locally | Same theorem and definition; no adaptation required. |
| Sheaf.Paper.ModuleCupCochainComparisonSquares | quarantined; holder not recorded locally | Same theorem and definition; no adaptation required. |
| Sheaf.Paper.ModuleCupAdjunctionPolygon | quarantined; holder not recorded locally | Same theorem and definition; no adaptation required. |
| Sheaf.Paper.ModuleCupCochainCounitTensor | quarantined; holder not recorded locally | Same theorem and definition; no adaptation required. |

These are all direct importers in lean/ and quarantine/. There are no current
Lean importers in lean/. The item remains needed by the quarantined consumers
and the existing DAG dependencies. No consumer, statement, definition, target,
node attachment, or proof dependency changes. An isolated public consumer checks
that the ring map and both public declarations are accessible through the
restored module.

## Status

landed 20261020T162541-L-3620879 2026-10-20 (merge of deliver/G1/Sheaf.Paper.ModuleCupGlobalTensorPullback)
