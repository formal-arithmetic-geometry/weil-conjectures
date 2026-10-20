## What changed

Proved `AlgebraicGeometry.Etale.derivedExchangeCube` in
`lean/Sheaf/SecSmoothPurity/DerivedExchangeCube.lean`, preserving its signature.
The proof applies `derivedBaseChangeMapPlus_paste_horiz` to both routes around the cube,
then cancels the derived inverse-image composition isomorphisms. The private, proved
helper `pasteHoriz` evaluates that existing pasting law at an object with specified
composites. The file now has the required module header and imports the horizontal
pasting theorem privately. The node's proof and proof dependencies follow this route.

Change record: `coord/changes/derived-exchange-cube-import.md`.

## Proved and sorry left

Closed the one original hole, `AlgebraicGeometry.Etale.derivedExchangeCube`
(node `lem-kun-derived-exchange-cube`). Zero holes remain in the item; zero holes are
added and no statements are split off. The private helper is also proved.
Single-file compilation passed with no errors or warnings. `#print axioms` reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the import `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`.
The proof no longer needs `lem-weil-pbc-derived-inverse-image-composition` as a separate
proof dependency, nor `lem-weil-pbc-mate-pasting` (Mathlib
`CategoryTheory.mateEquiv_vcomp`): the source library's proved horizontal pasting law
already includes the mate calculation. Removed both obsolete top-level `tool_uses`
approvals. The inverse-image composition notion remains a statement dependency because
the theorem's signature uses its canonical comparison isomorphisms.
No library modules are withdrawn. The only non-elementary proof dependency is
`lemma-weil-pbc-derived-exchange-coherence`, realized by
`WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal`.

## Where the brief, the DAG or earlier work was wrong

The old route unnecessarily expanded the four exchanges as adjunction mates.
The existing `derivedBaseChangeMapPlus_paste_horiz` proves both routes equal to the
same outer exchange, so no new intermediate theory is needed. The unit's statement
and proof steps are preserved; this changes only the route of its cube-coherence lemma.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
