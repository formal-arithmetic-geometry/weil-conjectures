## What changed

The derived signed-shift proof is organized into two strictly smaller obligations. `derived_shift_model` records the equation on K-injective localized representatives, and `derived_shift_descent` records the localization step from those representatives to arbitrary derived objects. The item theorem imports both modules and combines them without changing its statement.

## Proved and sorry left

The item theorem `derived_shift_part` is proved by applying the two named obligations. Two sorries remain, both split into new modules: `derived_shift_model` (node `lem-pod-reindexing-shift-derived-model`) and `derived_shift_descent` (node `lem-pod-reindexing-shift-derived-descent`). No sorry occurs in a definition.

## No longer needed

No former proof import was removed. The item now uses only `PodReindexingCoherenceData` plus the two new proof modules; the parent presentation definitions remain required.

## Where the brief, the DAG or earlier work was wrong

The public `Comparison` interface exposes the representative factorization and the derived natural isomorphism, but it does not expose the normalized source-shift naturality used by the blueprint. The proof therefore has two independent lower obligations: representative signed-shift compatibility and localization descent. Both are strictly smaller than the displayed universal square.

## New nodes

`lem-pod-reindexing-shift-derived-model` records the K-injective representative equation and is stated in `Sheaf.Paper.PodReindexingShiftDerivedModel`.

`lem-pod-reindexing-shift-derived-descent` records descent of that equation through localization and is stated in `Sheaf.Paper.PodReindexingShiftDerivedDescent`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PodReindexingShiftDerivedDescent": "8e64e475ec8cd24d0c528d40342d7e822fca6dbd", "Sheaf.Paper.PodReindexingShiftDerivedModel": "45e57df16d485075223dd39a9f5eef7c8882ddb4", "Sheaf.Paper.PodReindexingShiftDerivedPart": "da666c7f281933c21777051b085810849d33b613"}, "results": {}, "time": "2026-10-28T08:08:17+0800", "transitive": 0, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
