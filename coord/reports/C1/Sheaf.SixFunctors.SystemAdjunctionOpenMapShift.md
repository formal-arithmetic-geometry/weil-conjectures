## What changed

The item module now assembles `SystemAdjunctionOpenShift` from three named component
lemmas. The original target theorem is proved by this constructor assembly. The three
component proofs are split into named public theorems with documented source and
blueprint references; their statements are strict components of the target structure.

## Proved and sorry left

Closed the original hole in `WeilConjectures.IntegralSystemRealization.systemAdjunctionOpenMapShift`.
The target proof is a complete constructor assembly. Three component holes remain:
`systemAdjunctionOpenMapShift_generators`,
`systemAdjunctionOpenMapShift_adjunctionClauses` and
`systemAdjunctionOpenMapShift_inverses`, each recorded by a new DAG node.
This is a decomposition: the target structure is assembled from its three independent
component statements, each strictly simpler than the whole structure.

## No longer needed

No imports were removed. Every existing proof dependency remains relevant to at least
one split component. No existing node or module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan expands several independent compatibility clauses but the item
had only one aggregate hole. The component split makes those obligations independently
provable while keeping the target statement and unit route unchanged.

## New nodes

Added three component nodes under `sec-smooth-purity`:
`lem-pur-system-adjunction-open-map-shift-generators`,
`lem-pur-system-adjunction-open-map-shift-adjunction-clauses`, and
`lem-pur-system-adjunction-open-map-shift-inverses`. Each node records its source,
proof dependencies, searches, and exact Lean declaration. The interface change record
is `coord/changes/system-adjunction-open-map-shift-components.md`.

## Second reading by C1

No separate worker reading is available for this dispatched item; the maintainer's
independent stage-3 review is the required reading. The split declarations are named,
strict field components, and the target constructor preserves the original statement.
