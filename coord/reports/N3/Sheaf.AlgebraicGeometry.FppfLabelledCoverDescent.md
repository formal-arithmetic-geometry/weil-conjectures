## What changed

Proved `AlgebraicGeometry.Scheme.fppf_labelled_cover_descent` with its statement unchanged.
The pieces are the specified unions of open images. Empty mixed pullbacks imply their
pairwise disjointness; their complements are unions of other pieces. Open-cover morphism
gluing proves the coproduct property for arbitrary label universes, without a Small binder.
`IsOpenImmersion.lift` constructs the factorizations over S. Each label subtype is jointly
surjective onto its piece, and its maps are flat and locally finitely presented because
the identity/factorization square is a pullback along the monic open inclusion. The
Type-valued sheaf axiom then supplies the unique component section.

Added the proof-only import `Mathlib.AlgebraicGeometry.Limits` for the initiality of an
empty scheme. Removed the unused public import `Sheaf.CategoryTheory.SiteCoveringAxioms`;
the statement uses Mathlib's existing Sheaf, not IsSiteForCoverings. All other imports
are used. Updated the item's DAG proof and dependency list to match this construction.
No definitions, signatures, target statements, or source-library modules changed.
Change record: `coord/changes/N3-fppf-labelled-cover-unused-site-import.md`.
The downstream check found zero consumer modules; no adaptations are needed.

Checked the empty label/member/cover cases: all unions and subtypes permit empty types;
the empty cover is handled by the same sheaf axiom; gluing on mixed empty overlaps uses
the initiality of the empty scheme. Compiled on the project server without warnings. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.fppf_labelled_cover_descent`
(node `lem-trf-fppf-labelled-cover-descent`). Added zero holes; zero sorry declarations
remain in the delivered module. No split-off statements. The proof uses Mathlib and
contains no project theorem dependencies with sorry.

## No longer needed

Removed import `Sheaf.CategoryTheory.SiteCoveringAxioms`; its site-axiom definition is
unused by this theorem. The conceptual dependency `def-weil-pbc-sites-and-cohomology`
remains for the existing Mathlib Type-valued sheaf axiom.

Removed proof dependencies `lem-weil-pbc-open-immersion-base-change`,
`lem-weil-pbc-open-immersion-iso-onto-image`, and `lem-trf-fppf-covering-base-change`.
Direct open-immersion lifting gives the factorization, and the identity/monomorphism
pullback square gives base-change stability for each member of the label subcover.
No project Lean module realizes these three Mathlib leaves; none is withdrawn.
Every other original node dependency remains used; the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or source error found. Steps 3 and 5 of the plan were longer than
necessary: explicitly forming pullbacks, discarding empty members, and constructing
comparison isomorphisms can be replaced by direct lifting and compatibility tested on
arbitrary cones. The existing arbitrary index universes are preserved throughout.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
