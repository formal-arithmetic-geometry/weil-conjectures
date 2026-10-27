## What changed

Closed `properComponent_fixed_realization_core` by factoring its explicit
`properComponent` expansion into the new lower theorem
`properComponent_fixed_realization_expanded`. The core proof is a real
simplification and application of that expanded coordinate statement. The existing
wrapper theorem remains proved by the core identity. Added the expanded theorem
module and its DAG node; no public target statement was changed.

## Proved and sorry left

Closed one original hole:

- `WeilConjectures.CompactSupportFiniteProjection.properComponent_fixed_realization_core`
  (node `lem-sf-finite-proper-projection-fixed-realization-core`).

One lower intermediate hole remains:

- `WeilConjectures.CompactSupportFiniteProjection.properComponent_fixed_realization_expanded`
  (`sorry`, node `lem-sf-finite-proper-projection-fixed-realization-expanded`).

No other holes were added.

## No longer needed

The exploratory `Sheaf.Paper.ProjectionFormulaCoherence` import and the private
component expansion helper were removed; neither is used by the delivered proof.
The public `Sheaf.Paper.FiniteProjectionFixedCoordinates` import remains required by
the declarations. No existing DAG nodes or modules were pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery had already proved the wrapper but left the expanded core
calculation as a separate admitted step. The current delivery makes that split
explicit: the core now combines the concrete `properComponent` expansion with the
lower coordinate calculation, while preserving both original theorem statements.

## New nodes

`lem-sf-finite-proper-projection-fixed-realization-expanded` records the expanded coordinate calculation; its Lean declaration is in `Sheaf.Paper.FiniteProperProjectionFixedRealizationExpanded`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteProperProjectionFixedRealization": "4bc6eddeef30f4b992bbb8b0c4430f9fcb9f01a5", "Sheaf.Paper.FiniteProperProjectionFixedRealizationExpanded": "bd7f827151ba25f881ac42a9e10a9f1e1e11c858"}, "results": {}, "time": "2026-10-28T02:32:25+0800", "transitive": 0, "version": 1}
```

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
