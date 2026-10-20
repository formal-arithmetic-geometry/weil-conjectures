## What changed

Proved `CategoryTheory.inverseSystemSitePoint` in
`Sheaf.TraceFormula.InverseSystemSitePoint`, preserving all public signatures and definitions.
Added three proof-only Mathlib imports for preservation under colimits, cofiltered categories
of elements, and the skyscraper adjunction. Added proved private helpers for representatives,
eventual equality, lifting through topology saturation, the initial neighbourhood functor, and
the canonical natural stalk comparison. Updated the existing node proof to match this route.

Repair of returned head `ea940d8a0a`: removed `set_option warn.sorry false`.
The landing hole census matched the option name at line 33 as an unattributed hole.
The module now contains no hole markers and no local suppression of hole warnings;
the completed proof is retained. No tool or launcher script was changed.
Change record: `coord/changes/inverse-system-site-point-warning-option.md`.
The required downstream scan lists `Sheaf.AlgebraicGeometry.ProEtaleEnoughPoints`
(G4), `Sheaf.CategoryTheory.Sites.FinitarySliceEnoughPoints` (H3), and
`Sheaf.Paper.FinitarySiteEnoughPoints` (J4); no consumer requires adaptation.

The geometric morphism has exactly `inverseSystemSectionColimitFunctor` as inverse image.
Its adjunction is transported from the Mathlib skyscraper adjunction along a natural
isomorphism obtained from the initial inverse-system neighbourhood functor. No arbitrary
witnesses of unproved existence theorems are chosen.

Validation after repair: the complete module compiles cleanly through `lcompile.py`
(1.6 seconds).
`#print axioms CategoryTheory.inverseSystemSitePoint` reports exactly `propext`,
`Classical.choice`, and `Quot.sound` (separate successful 1.6-second compile).
Edge cases: empty covers are handled by the original lifting assumption; nonempty directed
indices ensure filtered colimits preserve terminal objects; transition maps need not be mono;
the natural comparison works with sheaf values in `Type (max u w)`.

## Proved and sorry left

Closed: `CategoryTheory.inverseSystemSitePoint` (node
`lem-trf-inverse-system-site-point`), the module's sole original hole.
Added holes: none. Remaining holes: none. All private helpers are proved.
The return's unattributed marker was the removed option name, not a proof hole.

## No longer needed

No imports, dependency nodes, or modules are pruned. All six recorded proof dependencies
remain used. The explicit quotient construction, elementwise inverse stalk comparison, and
handwritten skyscraper gluing/adjunction are supplied instead by proved Mathlib results:
colimit representatives and eventual equality, `Functor.Final.colimIso`, and
`Point.skyscraperSheafAdjunction`. No project lemma is imported with an unfinished proof.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery retained a local warning-suppression option whose name was
misclassified by the landing census. Removing that option repairs the returned
packet without changing a declaration, its statement, or its proof.

No statement error. The DAG described an explicit comparison without cofinality; proving
the canonical inverse-system neighbourhood functor initial gives the same natural comparison
more directly. Cover lifting extends to the generated Grothendieck topology by saturation
induction, so the proof does not need the additional site-axiom hypothesis `hJ`; its binder
and the complete public statement are retained unchanged.

Searches run through `msearch.py`: LeanFinder for a cofiltered system's site point and section
colimit; Loogle for finite-limit preservation and colimits; grep for the initial-functor and
colimit-comparison APIs. Read the cited dependency signatures and Stacks 00YC, 00Y7, 00Y8,
00YA(1), and 00YQ, together with Mathlib's corresponding proved implementations.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
