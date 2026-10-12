## What changed

Added an induction proof of `IsLocalRing.exists_finite_free_resolution_data`. The base and successor constructions are isolated as named intermediate theorems, each documented as a stage-3 decomposition and recorded as a DAG node.

## Proved and sorry left

The target theorem is proved by induction from `exists_finite_free_resolution_data_zero` and `exists_finite_free_resolution_data_succ`. The two intermediate construction theorems retain `sorry`, with nodes `lem-weil-pbc-cm-local-free-resolution-construction-zero` and `lem-weil-pbc-cm-local-free-resolution-construction-succ`.

## No longer needed

None; all original imports remain available to the intermediate construction statements.

## Where the brief, the DAG or earlier work was wrong

The original node's multi-step construction could not be completed within this item; the base and successor steps are therefore explicit strictly smaller obligations.

## New nodes

`lem-weil-pbc-cm-local-free-resolution-construction-zero` and `lem-weil-pbc-cm-local-free-resolution-construction-succ`, recorded under `dag/nodes/sec-proper-base-change/`.

## Second reading by F2

1. **Visible changes.** Compared with the repository module, only the induction proof and the two explicitly named intermediate declarations were added; the target signature and existing imports are unchanged.
2. **Compilation and axioms.** The delivered module compiles with `lcompile.py`. The only remaining holes are the two named construction theorems; there are no axioms, unsafe declarations, or hollow definitions.
3. **Statements and nodes.** The target statement is byte-for-byte unchanged. The zero and successor statements are genuine strictly smaller construction obligations, with source, documentation, and matching DAG nodes; neither duplicates an existing library declaration.
4. **Pruning.** Every existing import remains available to the intermediate construction statements, and no import or proof dependency was removed. The target proof follows the unit's induction route through the two construction steps.
5. **DAG agreement.** The parent node records the induction proof and depends on the two construction nodes; the construction nodes record their direct finite-free construction dependencies and do not depend circularly on the parent.

I changed the DAG proof metadata to remove the circular parent dependency from the two split nodes and to record the induction route in the parent. No Lean statement or import was changed.
