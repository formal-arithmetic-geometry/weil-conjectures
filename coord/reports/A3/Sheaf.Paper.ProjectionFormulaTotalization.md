## What changed
Added two strictly smaller conjunct lemmas as explicit proof splits and proved the target theorem by combining them. The target module imports the two auxiliary modules.

## Proved and sorry left
The target theorem `SheafOfModules.ringedProjectionFormula_totalization` is reduced to the two named conjunct lemmas. The new declarations `SheafOfModules.ringedProjectionFormula_totalization_left` and `SheafOfModules.ringedProjectionFormula_totalization_right` remain as the only two `sorry`s, each with its own DAG node, because the representative-level comparison and cancellation argument could not be completed in this session.

## No longer needed
No imports or existing proof dependencies were pruned; the target's declared route remains available to the split lemmas.

## Where the brief, the DAG or earlier work was wrong
The DAG's five-step representative proof requires a substantial comparison-square calculation not exposed as a single reusable theorem in the imported interface. The delivery makes the two inverse equations explicit split nodes so that this calculation can proceed independently.

## New nodes
`new-lem-weil-pbc-projection-formula-totalization-left` and `new-lem-weil-pbc-projection-formula-totalization-right` are the two conjunct statements used by the target proof.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
