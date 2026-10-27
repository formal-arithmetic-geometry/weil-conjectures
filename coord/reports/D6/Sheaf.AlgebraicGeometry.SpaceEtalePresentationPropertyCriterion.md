## What changed

Proved both theorems in `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`
without changing their statements, the locality predicate, the presentation structure, or
its existential property. The proof follows the six steps of
`lem-sfb-space-etale-presentation-property-criterion`.

Private helpers transport scheme-test properties across the canonical Yoneda isomorphism,
construct the tests of scheme morphisms, compose representable surjections, and prove
permanence in a non-cartesian étale square using the graph into the scheme pullback.
The source and target atlases yield a surjective presentation. A common refinement of two
presentations gives the pointwise witnesses required by locality. Identity presentations
and the same square argument give both equivalences for schemes.

The proof uses the existing `isEtale_comp` theorem and Mathlib pullback, Yoneda,
étale cancellation, and surjectivity APIs. No data are selected from unproved existence
statements. In particular, source and target pullback witnesses are eliminated only inside
propositions. The empty-source case is included: pointwise detection has no points to check.
Target charts are never assumed surjective in the comparison argument.

## Proved and sorry left

Closed both original holes (2 of 2):

- `AlgebraicGeometry.AlgebraicSpace.etalePresentation_property_criterion`.
- `AlgebraicGeometry.AlgebraicSpace.etalePresentation_property_iff_scheme`.

No holes remain in the item. No holes or split-off statements were added.
The final module compiles through `lcompile.py` in 4.9 seconds with no warnings.

## No longer needed

No DAG node or library module is pruned: all eight planned proof dependencies are used
through the existing algebraic-space definition and Mathlib APIs. No new proof-dependency
module is necessary. The proof replaces the private `Mathlib.CategoryTheory.Yoneda` import
with `Mathlib.CategoryTheory.Limits.Yoneda` for preservation of scheme pullback squares.
Removed the unused private import `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`;
the proof uses the direct scheme surjectivity API rather than covering-family membership.

## Where the brief, the DAG or earlier work was wrong

No statement or definition defect was found. The source argument and DAG plan work as
stated. The comparison helper applies directly to presheaves with representable étale
charts; the algebraic-space hypotheses are needed for existence of the initial atlases.
LeanFinder and Loogle searches found no direct criterion; source searches found existing
private proofs of the chart-construction patterns, which were adapted locally without
changing shared dependencies.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
