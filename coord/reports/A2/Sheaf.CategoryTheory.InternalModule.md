## What changed

Filled the two proofs in `lean/Sheaf/CategoryTheory/InternalModule.lean`.
`CategoryTheory.InternalModule.isHom_id` uses the categorical identity laws and
`CategoryTheory.Limits.prod.map_id_id`. `CategoryTheory.InternalModule.isHom_comp`
substitutes the two morphisms' compatibility equations for addition, zero,
negation and scalar multiplication, using associativity and
`CategoryTheory.Limits.prod.map_map` for addition.

The definitions, statements, category instance, forgetful functor, public imports
and declaration visibility are unchanged. The proofs follow the existing
docstrings and the node's stated category construction; no route change or node
edit is needed. The assigned module compiled successfully through `lcompile.py`.

## Proved and sorry left

Closed 2 of 2 holes:

- `CategoryTheory.InternalModule.isHom_id`
- `CategoryTheory.InternalModule.isHom_comp`

Both belong to node `def-pod-internal-module`. No `sorry` remains in the item.
No holes were added and no statements were split off.

## No longer needed

None. There were no proof-dependency imports or proof-dependency nodes to prune.
The existing public imports support the unchanged statements and definitions.
No new imports or modules were needed.

## Where the brief, the DAG or earlier work was wrong

None. The node is a definition node with empty `proof` and `proof_deps`; the
existing theorem docstrings already describe the two elementary proofs exactly.
Mathlib search found the required product identity and composition laws.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
