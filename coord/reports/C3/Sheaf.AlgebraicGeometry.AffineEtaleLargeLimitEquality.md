## What changed

Proved `AlgebraicGeometry.ProEtale.affineEtale_largeLimit_eventualEquality` in
`Sheaf.AlgebraicGeometry.AffineEtaleLargeLimitEquality`, with its statement,
universes, public import and visibility unchanged. Four fully proved private
helpers establish finiteness of étale geometric lift sets, existence of a
nonempty geometric cone, and the open-and-closed agreement locus. The proof uses
constructible compactness and compatible finite geometric lifts, then the given
limit universal property. Updated the theorem docstring and its node's proof,
proof dependencies and proof origin to describe this route.

Added only private proof imports of `Mathlib.CategoryTheory.CofilteredSystem`,
`Mathlib.Topology.Spectral.ConstructibleTopology`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
No other existing module or shared interface changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.affineEtale_largeLimit_eventualEquality`
(node `lem-pe-affine-etale-large-limit-equality`). Added 0 holes; 0 holes remain
in the delivered module. No split-off obligations.

Remote single-file compilation passed without warnings in 3.9 seconds.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
The proof also covers empty stages: assuming failure of every refinement forces
each complementary pullback to be nonempty, so that case cannot enter the
compactness argument. The given limit's vertex is never assumed affine or étale.

## No longer needed

The old planned dependency
`lem-weil-pbc-locally-finite-type-limit-map-equality` and its Mathlib theorem
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType` in
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` are unnecessary for this
proof. Removed that node from this node's proof dependencies. Its module was not
an original import and has not been withdrawn; other users may still need it.
The general finite-generator/affine-colimit route is entirely bypassed below the
unit level. No existing public import was removed, and no module was deleted.

During proof development, removed redundant private imports of
`Mathlib.AlgebraicGeometry.Morphisms.Separated`,
`Mathlib.AlgebraicGeometry.Sites.EtalePoint`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified`;
the needed declarations are available through the retained imports. Replaced
`WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology` by its Mathlib
counterpart, which supplies all the topology results used here.

## Where the brief, the DAG or earlier work was wrong

The old proof invoked a small-index affine limit equality theorem in a larger
index universe. Its finite-witness explanation did not provide the missing
universe-compatible colimit argument. The statement is valid: the affine étale
hypotheses give finite geometric lift sets, and Mathlib's finite cofiltered-system
theorem allows the larger index universe directly. The updated node records
this complete replacement argument. The blueprint unit route and all existing
statements remain unchanged.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
