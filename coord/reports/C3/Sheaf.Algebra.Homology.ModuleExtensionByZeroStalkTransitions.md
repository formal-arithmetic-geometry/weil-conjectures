## What changed

Withdraw `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkTransitions`, a zero-hole
retirement item. Redirect `lem-sc-module-extension-by-zero-stalk-maps-transitions` to
`AlgebraicGeometry.moduleExtensionByZero_stalk_transitions` in the upstream twin.
Its signature is identical after the declaration rename. Preserve the node's proof,
proof dependencies and mathematical statement. No upstream or consumer source edits.

The exact former statement compiles by applying the upstream theorem (2.7 seconds).
The unchanged upstream caller `module_extensionByZero_stalk_maps` compiles (4.1 seconds).
Both axiom checks report only propext, Classical.choice and Quot.sound.

Change record: `coord/changes/C3-retire-module-extension-by-zero-stalk-transitions.md`.

## Proved and sorry left

Original item: zero sorries. Holes closed: zero. Holes added: zero. Split off: zero.
No sorry remains or is added by this delivery. The mathematical assertion remains
proved as `AlgebraicGeometry.moduleExtensionByZero_stalk_transitions`, with the same
statement and the allowed axioms only. This is a duplicate retirement, not new proof work.

## No longer needed

Pruned module: `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkTransitions`, including
its duplicate `AlgebraicGeometry.ModuleExtensionByZeroStalkTransitions` declaration.
No external import lines need removal: source scans and downstream.py find zero
consumers of the retired copy. Its upstream twin remains in use by the upstream
ModuleExtensionByZeroStalkMaps module. No mathematical dependency node is pruned;
the existing node is retained and reattached to the upstream theorem.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a hole, whereas the live queue marks this item
`retire` with zero holes. The inventory lists Sheaf ModuleExtensionByZeroStalkMaps as
a consumer, but that module has already been retired in the shared tree. The claimed
missing API is a rename: upstream provides `moduleExtensionByZero_stalk_transitions`
with precisely the old statement. The node's former lean.declaration already named
the lowercase upstream theorem while its lean.module incorrectly pointed at the
capitalized copy; this attachment is now consistent. No statement, definition, unit
route or target changes, and no new nodes.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
