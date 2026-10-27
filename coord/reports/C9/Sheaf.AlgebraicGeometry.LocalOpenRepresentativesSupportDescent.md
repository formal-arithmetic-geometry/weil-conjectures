## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.localOpenRepresentatives_support_descent` with a proof.
For arbitrary maps to two covering members with the same composite to the base,
evaluate the first representing isomorphism on the inverse-image open and use
the second inverse isomorphism to obtain a factorization through the second open.
The triangle identity proves containment. Applying this in both directions to
the fibre-product projections proves overlap equality. Etaleness supplies flatness
and local finite presentation; the given joint surjectivity makes the family fppf.
Mathlib's fppf-to-fpqc comparison and the existing
`AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc` finish the proof.

Validation: the remote single-file compiler accepted the complete proof in 2.7 seconds
with exit code 0 and no warnings.

The statement and public imports are unchanged. Updated the item's DAG proof to
record the general containment argument and its exact dependency set.

## Proved and sorry left

Closed: `AlgebraicGeometry.localOpenRepresentatives_support_descent`
(node `lem-trf-local-open-representatives-support-descent`), one of one original holes.
Added: no holes. Left in the delivered modules: none. No decomposition or new nodes.
The proof uses the existing fpqc open-subscheme descent theorem as authorized.

## No longer needed

The item's proof no longer needs node
`lem-weil-pbc-open-immersion-base-change`: inverse-image opens are constructed
directly, and their maps to the representing opens use the open-immersion lifting
property. Removed this node from the item's `proof_deps` and proof-step `uses`.
No imports or entire modules were removed; `Mathlib.AlgebraicGeometry.OpenImmersion`
is still needed for the lifting property. All other declared dependencies are used.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The explicit base-change construction in the old DAG
is unnecessary. The arbitrary-presheaf evaluation argument is valid: the equality
of composites identifies exactly the two over-objects on which F is evaluated.
No sheaf condition or compatibility of the representing isomorphisms is used.
The empty covering is included, since the fppf cover criterion and the existing
fpqc descent theorem both allow it. Universes and all hypotheses are preserved.

Sources read: spaces-descent.tex, lemma-descending-property-open-immersion
(Tag 041X), and descent.tex, lemma-open-fpqc-covering (Tag 03N0).
Read the latest blueprint unit sk-i-curve-zero and its realization record;
this change bypasses no unit statement or unit proof step.

Searches: LeanFinder for overlap equality of locally represented opens returned
scheme-restriction and gluing lemmas, with no direct replacement. Loogle for
`AlgebraicGeometry.Scheme.Opens.lift` reported an unknown identifier.
The grep search for `homToPreimage|ofArrows_mem_precoverage` found the exact
cover-membership criterion in Mathlib's Sites/MorphismProperty. Local searches
located `IsOpenImmersion.lift` and `IsOpenImmersion.lift_fac` and confirmed the
existing fpqc descent theorem, which are used directly.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
