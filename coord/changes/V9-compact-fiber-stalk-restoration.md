# WeilConjectures.PurityFiniteSetting.compactFiber_qbar

## Reason

Restore the quarantined `Sheaf.Paper.CompactFiberStalk` module recorded in `coord/rework.tsv` and repair elaboration of its final dependent conjunction. The combined tuple attempt exhausts the existing 10000-heartbeat bound at its final projection. Splitting the conjunction avoids the expansion and compiles in 50.4 seconds. This is a proof-only repair; there is no definition or statement change.

## Old

The live source is absent. The archive is `quarantine/Sheaf/Paper/CompactFiberStalk.lean` with unchanged signature:

```lean
theorem compactFiber_qbar : CompactFiberQbarFormula P f Omega s := by
```

Its final proof line is:

```lean
  exact ⟨h.1, fun D K ↦ (h.2 D).2.2.1 K⟩
```

## New

The same module is restored at `lean/Sheaf/Paper/CompactFiberStalk.lean`, with the identical signature:

```lean
theorem compactFiber_qbar : CompactFiberQbarFormula P f Omega s := by
```

Only the final proof term changes:

```lean
  constructor
  · exact h.1
  · intro D
    exact (h.2 D).2.2.1
```

Every other declaration, definition, attribute and import is retained verbatim from the archive. The node's proof records the elaboration repair; its attachment and dependencies remain unchanged.

## Users

`tools/downstream.py Sheaf.Paper.CompactFiberStalk --uses compactFiber_qbar` reports unknown module because the live file is quarantined. Direct searches for imports and declaration uses in `lean/` and `quarantine/` find no current Lean consumers. The following DAG parents retain their dependencies and require no source edits.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactFiberStalk | V9 | Restore the full archived module and repair the final proof; identical public interface. |
| lem-pur-line-zero-class-exchange (DAG parent) | not adapted | Identical statement and canonical exchanges; dependency retained. |
| thm-pur-rank-one-thom (DAG parent) | not adapted | Identical statement and canonical exchanges; dependency retained. |
| thm-pur-vector-bundle-thom (DAG parent) | not adapted | Identical statement and canonical exchanges; dependency retained. |

No target statement or definition changes. No forced adaptations.

## Status

landed 20261023T152118-L-449756 2026-10-23 (merge of deliver/V9/Sheaf.Paper.CompactFiberStalk)
