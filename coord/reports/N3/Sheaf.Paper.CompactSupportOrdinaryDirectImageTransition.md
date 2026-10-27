## What changed

Proved `WeilConjectures.compactSupportOrdinaryDirectImageTransition` in its original
module with its statement unchanged. Added a proof-only import of
`Sheaf.Paper.CompactSupportOrdinaryDirectTransition`. Postcomposing with the
level-m `compactSupportDirectModel` comparison identifies the desired equation
with the existing proved square in constant-module coordinates: expand the scalar
comparison, cancel the inverse model comparison, and use naturality. Updated the
item node to record this route. The categorical transport is proved once as the
private helper `transportDirectImageSquare`, so concrete coefficient definitions
stay outside rewrite matching. Local reducibility attributes follow the adjacent
ordinary direct-evaluation modules; shared definitions remain unchanged.
No shared interfaces or other modules changed.

Validation: the item compiled through `lcompile.py` in 19.1 seconds, below the
60-second per-file limit. The import-direction check permits the proof import.

## Proved and sorry left

Closed the sole hole, `WeilConjectures.compactSupportOrdinaryDirectImageTransition`
(node `lem-weil-compact-support-ordinary-direct-image-transition`).
Holes closed: 1 of 1. Holes added: 0. No `sorry` remains in the delivered module.
No statements were split off.

## No longer needed

No imports or modules were removed. The direct sectionwise recalculation in the
old proof plan is unnecessary: its two half-calculations are already proved under
`lem-weil-compact-support-ordinary-direct-transition`. The nodes
`def-sp-varying-ring-operations` and
`lem-weil-compact-support-coefficient-transition` remain statement dependencies
and are used by that existing square, but are no longer separate direct proof
steps of this item. Nothing is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The old plan did not exploit the existing proved square
`WeilConjectures.compactSupportOrdinaryDirectTransition`. Its constant-module
coordinates differ from this statement only by the specified
`compactSupportDirectModel` isomorphisms. Thus another geometric split is
unnecessary. The node statement and the unit route are preserved.

A read-only dependency traversal also found an existing DAG cycle through
`lem-weil-compact-support-coefficient-transition`, the reduction-tower definitions,
and the ordinary pullback/open-transition route back to this item. The original
item already listed the coefficient-transition node in both statement and proof
dependencies. This delivery leaves statement dependencies untouched and does not
repair unrelated node records. The actual Lean import-direction check allows the
new proof import: the reused theorem does not import this item.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
