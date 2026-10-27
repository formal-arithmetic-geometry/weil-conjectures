# SheafOfModules.product_tensor_test_bounds

## Reason

The proof treats the published derived tensor as a fixed bifunctor and uses its proved
API. A local irreducibility attribute prevents elaboration from expanding the nested
existence choices used to construct it. Preflight conservatively classifies this new
module command as an interface change, so this record explicitly covers it.

## Old

No local transparency override in `Sheaf.Paper.ProductTensorTestBounds`; the published
`SheafOfModules.siteDerivedTensorIndependentCoefficients` has its original reducibility.

## New

```lean
attribute [local irreducible] siteDerivedTensorIndependentCoefficients
```

This is local to this file's section. It changes no definition body, theorem signature,
public import, exported attribute or mathematical statement. In particular the theorem's
entire original signature and all four conclusion clauses remain verbatim. The tensor
itself is still the published construction, with no replacement or chosen model.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ProductTensorTestBounds | Y3 | Local proof elaboration only; one hole closed. |

`python3 tools/downstream.py Sheaf.Paper.ProductTensorTestBounds --uses
SheafOfModules.product_tensor_test_bounds` reports zero downstream modules and only
the declaration's own module as a textual user. A direct Lean-tree search confirms
that there is currently no external importer or user of these declarations. No consumer
adaptation is necessary. No target signature or interpretation changes, so no target
statement review is reopened. The node remains attached and available to its unfinished
DAG parents; no withdrawal is proposed.

## Status

landed 20261023T103440-L-3141153 2026-10-23 (merge of deliver/Y3/Sheaf.Paper.ProductTensorTestBounds)
