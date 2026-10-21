## What changed

This is a zero-hole duplicate retirement. The complete adopted module
`WeilConjectures.AlgebraicGeometry.IrreducibleLisseRefinement` already provides
`AlgebraicGeometry.Scheme.exists_irreducible_refinement`. I withdrew the duplicate
Sheaf module via `deleted.txt`, changed the sole Sheaf consumer
`Sheaf.AlgebraicGeometry.IrreducibleLisseStrata` to import the adopted provider, and
rebound `lem-weil-pbc-irreducible-refinement` to the adopted declaration.

The migrated consumer compiles with its original theorem statement and proof. No
source-library declaration or target statement changed.

## Proved and sorry left

Initial holes in the item: zero. Holes closed: zero. Holes added: zero. No
split-off statements and no sorries remain in delivered modules. The retained
upstream theorem is complete and supplies the same mathematical result.

## No longer needed

The duplicate module `lean/Sheaf/AlgebraicGeometry/IrreducibleLisseRefinement.lean`
and its duplicate declaration and imports are no longer needed. Its adopted source
twin remains needed by the migrated Sheaf consumer. No mathematical DAG dependency
or unit step is pruned; the node is retained and reattached to the upstream theorem.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a module containing a `sorry`, but this queue item
is explicitly a `retire` item and the current module has zero holes. The adopted source
library now contains a complete twin, so proving the duplicate again would preserve
an unnecessary second provider. The historical node attachment still named the
duplicate Sheaf module; this delivery reconciles it with the retained source theorem.

## New nodes

None.

Change record: `coord/changes/irreducible-lisse-refinement-retire.md`.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
