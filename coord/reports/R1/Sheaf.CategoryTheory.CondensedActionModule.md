## What changed

Filled `Profinite.CondensedAction.equivariant_closure` in
`Sheaf.CategoryTheory.CondensedActionModule` with the direct sectionwise proof already
used by the universe-generalized counterpart in
`Sheaf.CategoryTheory.UniverseCondensedActionModule`. Identity is reflexivity;
composition substitutes the two equivariance equations; zero, addition and negation
use `map_zero`, `map_add` and `map_neg` for the linear action endomorphisms.
All signatures, definitions, instances and imports are unchanged.

## Proved and sorry left

Closed the sole original hole, `Profinite.CondensedAction.equivariant_closure`.
Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module.
No new intermediate statements or modules were needed.

## No longer needed

None. All original imports are retained for the existing statements and definitions.
The proof uses no additional project dependency. No node or module is withdrawn;
the universe-generalized module imports this specialized module, so it cannot be
imported back to reuse its theorem directly.

## Where the brief, the DAG or earlier work was wrong

The definition node `def-sfb-condensed-action-module` now attaches to the newer
universe-generalized interface, while the specialized module retains its own
closure theorem and existing consumers. The generalized closure theorem was already
proved, so its sectionwise argument also closes this older hole without changing
any interface or the unit route. No mathematical defect was found. No node update
is needed for this proof-only delivery.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
