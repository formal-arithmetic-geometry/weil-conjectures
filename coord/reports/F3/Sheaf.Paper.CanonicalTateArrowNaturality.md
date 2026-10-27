## What changed

Proved `WeilConjectures.CanonicalTate.ordinarySquare_existsUnique` using the existing
completed-coefficient direct-image compositors. Private helpers identify their maps and
inverses on sections and handle transport across equality of scheme morphisms. The direct
square is conjugated through the two composite module adjunctions. The adjunction-unit
identity gives exactly the specified double-unit section formula; injectivity of the
composite adjunction hom equivalence proves uniqueness. The calculation is proved
privately for the existing abstract coefficient structure with its composition law,
then specialized using `completedPull_comp`. A separate private categorical lemma
packages existence of the conjugate with its unit identity, avoiding expansion of
the concrete module inverse-image construction. Local irreducibility attributes keep the fibre-product isomorphisms abstract.
A generic comparator-square lemma eliminates the equality between the two composite
scheme maps before evaluating sections; an isomorphism equality identifies its site
square with `siteSquare`. Existing public signatures,
definitions and imports are unchanged.

## Proved and sorry left

Closed one of the item's two holes:
`WeilConjectures.CanonicalTate.ordinarySquare_existsUnique`.

The remaining hole is
`WeilConjectures.CanonicalTate.canonicalTateArrowNaturality`
(node `lem-pur-canonical-tate-arrow-naturality`); its statement and complete existing
nine-step proof plan are unchanged. No holes were added or split off. The already proved
`ordinaryScalarSquare_existsUnique` is retained unchanged.

## No longer needed

None. All public imports remain necessary for the existing statements and definitions;
the private cochain coefficient import is still used by the scalar adjunction proof.
No planned dependency is withdrawn: the main theorem remains open. Mathlib search found
generic pullback-composition and adjunction-mate lemmas, but no replacement for the
canonical Tate-arrow theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface discrepancy found. The ordinary square needs the completed
coefficient direct-image composition already provided by
`PurCompactSupport.modulePushComposition_existsUnique` and `completedPull_comp`;
constant-coefficient pullback composition alone would not identify these module functors.
The existing plan explicitly calls for this adjunction-normalized composition argument.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
