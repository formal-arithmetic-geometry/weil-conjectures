# cartier_equality

## Reason

Upstream review #1428 identified the former finite-type formulation as degenerate for a field extension. The repair makes finite generation of the top intermediate field explicit via `IntermediateField.FG`.

## Old

```lean
theorem cartier_equality
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (hfg : (⊤ : IntermediateField k K).FG) :
```

## New

```lean
theorem cartier_equality
    (k K : Type*) [Field k] [Field K] [Algebra k K]
    (hfg : IntermediateField.FG (⊤ : IntermediateField k K)) :
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.PthRootResidueDimensionBalance | unclaimed | Existing call with `IntermediateField.fg_top` remains type-correct. |

## Status

landed 20261014T042431-L-1211984 2026-10-14 (merge of deliver/V2/Sheaf.Paper.CartierEquality)
