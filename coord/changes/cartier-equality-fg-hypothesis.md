# Sheaf.Paper.CartierEquality

## Reason

Upstream review #1428 identified the old `[Algebra.FiniteType k K]` interface as weakened: for a field `K` it forces a finite extension and collapses the transcendence-degree assertion. The repaired interface uses finite generation of the field extension, `(⊤ : IntermediateField k K).FG`. The source branch already contained this correction; this delivery makes the equivalent qualified form `IntermediateField.FG (⊤ : IntermediateField k K)` explicit and records the repair for the queued item.

## Old

```lean
(hfg : (⊤ : IntermediateField k K).FG)
```

## New

```lean
(hfg : IntermediateField.FG (⊤ : IntermediateField k K))
```

The two forms are definitionally identical. No caller adaptation is required; `Sheaf.RingTheory.PthRootResidueDimensionBalance` continues to pass `IntermediateField.fg_top K L`.

## Users

`lem-weil-pbc-pth-root-residue-dimension-balance` is the only DAG caller. Its
existing `IntermediateField.fg_top` argument is definitionally compatible, so no
module adaptation is needed.

## Status

landed 20261013T201807-L-3976285 2026-10-13 (merge of deliver/Q4/Sheaf.Paper.CartierEquality)
No new theorem holes or imports were introduced.
