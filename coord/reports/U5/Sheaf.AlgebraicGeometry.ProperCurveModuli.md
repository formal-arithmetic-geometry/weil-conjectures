## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.ProperCurveModuli.hom_operations` with a complete proof.
The identity clause uses `CategoryTheory.IsPullback.id_horiz` and Yoneda's
`Functor.map_id`. The composition clause horizontally pastes the two cartesian
squares using `CategoryTheory.IsPullback.paste_horiz` and rewrites the bottom
edge using `Functor.map_comp`. All statements, definitions and imports are unchanged.
The existing docstring already describes this argument, and the definition node
`def-sfb-proper-curve-moduli` has no proof dependencies to change.

Searches used msearch.py LeanFinder, Loogle and grep, together with rg searches
of Mathlib, Sheaf and WeilConjectures. The fully qualified Loogle query found
`CategoryTheory.IsPullback.id_horiz`; LeanFinder and grep found horizontal pasting.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProperCurveModuli.hom_operations`
(blueprint: `def-sfb-proper-curve-moduli`), the module's only original hole.
Holes closed: 1. Holes added: 0. Holes left in the module: 0. Nothing split off.

## No longer needed

None. All existing imports support the module's statements and constructions.
No dependency nodes or modules are pruned. The proof uses Mathlib's existing
pullback lemmas through the current imports and needs no additional dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface discrepancy found. The definition node has an empty
proof list; its named `hom_operations` theorem's existing docstring gives the
identity and pasting argument, now formalized directly. No unit route is changed.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
