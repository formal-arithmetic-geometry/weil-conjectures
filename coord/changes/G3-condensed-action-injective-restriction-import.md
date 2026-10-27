# Profinite.CondensedAction.action_injective_restriction

## Reason

Restore the item from its quarantine archive, as assigned by coord/rework.tsv.
The archived file publicly imported CondensedProductActionInflation, which is
itself quarantined through CompletionUnitFiniteMateComparison. None of the
item's declarations or proofs uses a declaration from that import.
CondensedDerivedInvariants already supplies the action-category structures,
exact restriction instances, and derived functors used by this item.
Removing the redundant import restores a compilable source dependency closure.
No theorem statement, definition, attribute, or proof body changes.

## Old

```lean
public import Sheaf.CategoryTheory.CondensedProductActionInflation
```

## New

The import is removed. All other imports and all declarations are verbatim
from quarantine/Sheaf/CategoryTheory/CondensedActionInjectiveRestriction.lean.

## Users

The source index reports no live importers (`tools/downstream.py` with
`--allow-missing`). Searching quarantine as well finds the following two
direct importers; their original sources are checked against the restored
module, without including those unchanged copies in the delivery.
FreeParameterDegreeZeroData compiled alone in 27.4 s. The original
product-bar consumer first timed out at 62 s; its profiling version subsequently
compiled with exit 0 (12 s cumulative kernel checking, 6.64 s instance inference,
and 8.78 s linting). The expected profiling-option warnings are confined to
the discarded diagnostic copy. No semantic incompatibility was reported.
Neither importer names any declaration of CondensedProductActionInflation.
Both import this module privately, so removing the public reexport cannot
alter their public signatures. Their separate quarantine restorations remain
with their respective items.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.CondensedActionInjectiveRestriction | G3 | Restored with redundant public import removed; declarations unchanged. |
| Sheaf.CategoryTheory.CondensedProductBarResolutionModel | quarantined; no local claim found | Uses existing injective-restriction theorems; signatures unchanged. |
| Sheaf.Paper.FreeParameterDegreeZeroData | quarantined; no local claim found | Uses restriction_free_flat_comparison, whose complete signature is preserved. |

No target statement or definition used by a target changes.

## Status

landed 20261027T064451-L-2183428 2026-10-27 (merge of deliver/G3/Sheaf.CategoryTheory.CondensedActionInjectiveRestriction)
