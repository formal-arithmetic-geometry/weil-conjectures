# Sheaf.AlgebraicGeometry.GabberH0FiniteSection public imports

## Reason

The finite-section construction needs `etaleSetDescentUnit` and
`etaleSetDescentComparison`, both defined in `FiniteSurjectiveSetDescentInjective`.
It does not use the full descent equalizer theorem. Narrowing the import avoids
pulling that later descent step into this construction. No existing declaration
or definition changes. This record documents only the public import removal
required by the stage-3 preflight.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescent
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FiniteSurjectiveSetDescentInjective
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.GabberH0FiniteSection --direct
--uses finiteSurjectiveSetDescent` reports one direct importer and no uses of
that theorem in the item or direct importer. The direct importer uses a plain
proof import of this module, so the removed public import was not exposed
through it to the remaining downstream modules. It also directly publicly
imports `FiniteSurjectiveSetDescent` itself. The transitive `--uses finiteSurjectiveSetDescent` search also finds
`Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion`, which directly imports the
full descent module privately; its two uses are independent of this item.
No caller needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GabberH0EtaleCriterion | none recorded locally; no adaptation | Its private import of the full descent module supplies both uses independently. |
| Sheaf.AlgebraicGeometry.GabberH0FiniteLift | none recorded locally; no adaptation | Imports the item only for its unchanged theorem; has its own public import of the full descent module. |

The unchanged theorem signature uses only declarations still available from the
smaller import and the existing Mathlib imports. No target meaning changes or
statement-review reopening occurs. The two new modules have no existing users
and use the smaller import from their creation.

## Status

landed 20261012T095851-L-312145 2026-10-12 (merge of deliver/B2/Sheaf.AlgebraicGeometry.GabberH0FiniteSection)
