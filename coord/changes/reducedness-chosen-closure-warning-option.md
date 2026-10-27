# Algebra.isReduced_tensorProduct_chosen_algebraicClosure_iff

## Reason

Repair the landing rejection of delivery `b4adf541e05`: the hole census interpreted
the `sorry` component of the inherited warning-option name as an unattributed hole.
Remove the unnecessary warning suppression from this fully proved module. This
restores the default warning behavior; no mathematical statement, universe,
instance, declaration visibility, or public import changes. Preflight treats the
file-level command removal as an interface change and requires this record.

## Old

```lean
set_option warn.sorry false
```

## New

The option command is removed. All existing declaration signatures are unchanged.

## Users

`tools/downstream.py Sheaf.TraceFormula.ReducednessTensorChosenAlgebraicClosure
--uses Algebra.isReduced_tensorProduct_chosen_algebraicClosure_iff` reports zero
downstream modules and only the declaration's own occurrence. The DAG parent
`lem-trf-geometric-reducedness-algebraic-closure-test` still needs the unchanged
statement; it is not withdrawn or bypassed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.TraceFormula.ReducednessTensorChosenAlgebraicClosure | T2 | Remove warning suppression; theorem fully proved and signature unchanged. |

No consumer adaptations or target statement reviews are needed: no definitions
or theorem types change. The repaired module compiles with no diagnostics.

## Status

landed 20261023T124427-L-1398380 2026-10-23 (merge of deliver/T2/Sheaf.TraceFormula.ReducednessTensorChosenAlgebraicClosure)
