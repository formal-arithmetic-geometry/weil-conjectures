## What changed

Proved `AlgebraicGeometry.isExcellent_of_affine_open_cover` in
`Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover`, without changing its statement.
The proof obtains local Noetherianity from excellent chart rings, applies the existing
G-ring, J-2 and universal-catenarity locality declarations, and recombines their conclusions.
For universal catenarity it reindexes by `Set.range U`, accommodating the arbitrary universe
of the original index type without changing any dependency declaration.
For an affine open of an open subscheme, its image is affine in the ambient scheme,
and its section ring is definitionally the same ring.

Retained the three component-locality proof imports and added the direct Mathlib
Noetherian import. Updated the existing node's proof and proof dependencies to match.
The remote single-file compiler passed in 3.7 seconds with no diagnostics.
The argument uses no point choices, nonempty index assumptions, or nonempty-open assumptions;
empty schemes, covers and opens are covered by the same proof.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.isExcellent_of_affine_open_cover`
(node `lem-trf-excellent-scheme-affine-cover`). Zero holes remain in the item.
Added zero holes and split off zero statements. This is a proof from the existing
component-locality declarations, whose own proofs remain separate items.

## No longer needed

Removed the redundant private import `WeilConjectures.RingTheory.GRing`:
its definitions are already public imports of the statement's excellent-ring module.
The G-ring definition node `def-weil-pbc-g-ring` remains needed and remains in the DAG.

Removed `lem-weil-pbc-affine-opens-basis` from this node's proof dependencies:
images under the open-subscheme inclusion and definitional equality of section rings
prove the second conjunct directly, so no affine-basis refinement is needed.
All three component-locality nodes and their modules remain needed. No modules are
withdrawn, and no public imports, statements or definitions are changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The catenarity declaration's index type is
restricted to the universe of the scheme, whereas the item allows an arbitrary index
universe; reindexing by the range resolves the interface mismatch. The DAG's last step
used the affine-open basis, which is unnecessary for the stronger all-affine-opens
conclusion actually stated in Lean. The unit route is unchanged.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
