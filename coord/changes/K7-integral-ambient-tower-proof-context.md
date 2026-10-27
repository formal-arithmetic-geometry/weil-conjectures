# AlgebraicGeometry.Scheme.IntegralAmbientTower

## Reason

The item now proves all six existing theorems. Its proofs require the existing
coefficient-model definitions to unfold during backward elaboration, as in their
own defining modules. The obsolete instance-disable command referred to the
removed private CompletedCoefficientPushforwardComparison import. Dropping it
makes that unused import unnecessary. The static delivery gate classifies these
proof-context command differences as visible changes and requires this record.

The only added declarations are fully proved private theorem helpers. All existing
public signatures, definitions, attributes on declarations, and public imports are
unchanged. No source-library module, target statement, coefficient action, or
completion map changes. No consumer adaptation or target review is required.

## Old

The original proof-context commands, verbatim:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

The following command disabled an instance from a private proof import:

```lean
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.hasDerived
```

Every assigned theorem body was `by sorry`.

## New

The replacement file-local elaboration settings, verbatim:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The obsolete hasDerived attribute command is removed together with its private
proof import. The same two settings are explicitly scoped to the private
unit_of_iso_completion helper as well. All other existing context commands remain
unchanged. Four private, proved theorem helpers provide Roos-object isomorphisms,
countable products, and detection of the specified completion unit. Their signatures
are absent from all public signatures and definition bodies.

All six existing theorem signatures and all four existing definitions are verbatim
unchanged. Only their theorem proofs and private proof imports are replaced.
The protected RingedTowerPushforwardLimitComparison import is retained.

## Users

`python3 tools/downstream.py Sheaf.Paper.IntegralAmbientTowerComparison --uses
finiteResolution coefficientModel_exists encodings complete_iff comparison
etaleOriginComparison` reports zero downstream modules in the current source tree.
The declaration-name search finds only the assigned module itself. No other module
is edited or needs adaptation. Unfinished DAG parents retain the same public API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralAmbientTowerComparison | K7 | Six theorem proofs completed; same public API. |

## Status

landed 20261022T202031-L-1250403 2026-10-22 (merge of deliver/K7/Sheaf.Paper.IntegralAmbientTowerComparison)
