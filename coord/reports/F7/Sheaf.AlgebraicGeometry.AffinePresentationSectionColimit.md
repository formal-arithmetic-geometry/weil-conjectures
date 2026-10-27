## What changed

Implemented the proof of
`AlgebraicGeometry.ProEtale.affinePresentation_sectionCocone_isColimit` without
changing its statement or its existing public import.

The proof constructs affine-site membership of the vertex using a restricted
ring presentation and `CommRingCat.ind_etale_small_index`. It then takes a small
relative presentation and applies the given small filtered-colimit preservation.
The ring-colimit and vertex-membership arguments are proved private helpers,
following the already proved private construction in
`CoefficientComparisonPresentationSheafification` (that module is not imported).

A further proved private helper obtains small-index affine etale representable
continuity directly from `Scheme.preservesColimit_yoneda`. Both presentations
map finally into the same costructured-arrow category of affine etale objects
under the vertex. Two applications of `Functor.Final.isColimitWhiskerEquiv`
identify their actual restriction cocones. Thus no functor from a small category
cofinal in the original index is assumed.

Added the proof imports `AffineEtaleLargeLimitMaps`, `IndEtaleSmallIndex`, and
`WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful` (the last supplies
the existing fully faithful Hom comparison isomorphism). Added one geometric
lemma module for the larger-index representable continuity step and updated
the parent node to match the implemented proof.

## Proved and sorry left

Closed the original explicit hole in
`AlgebraicGeometry.ProEtale.affinePresentation_sectionCocone_isColimit`
(node `lem-pe-affine-presentation-large-continuity`): 1 of 1 original holes.
There are no explicit sorries in the item module.

Added one hole:
`AlgebraicGeometry.ProEtale.affineEtale_largeLimit_preservesColimit`
(node `lem-pe-affine-etale-large-limit-maps`), in its own module.
This is the geometric finite-presentation step only, concerning maps into an
affine etale object; it has no arbitrary sheaf or continuity hypothesis. All
small-presentation construction, application of hF, and comparison of section
cocones are proved in the item module. This is a decomposition (one hole closed,
one added), not a sorry-free proof of the original theorem or net hole progress.

## No longer needed

No existing imports were removed and no module is withdrawn. The basis theorem,
the small-index ring theorem, and the continuity-map definitions remain needed.
The direct elementwise surjectivity/injectivity chase in the old parent plan is
replaced by the two final-functor colimit equivalences. The small-index
factorization and equality results alone do not prove the larger-index
representable assertion: their Lean index universe is fixed to the scheme
universe. They remain used through Mathlib's proved small-index Hom continuity.

No declarations or public imports in `lean/WeilConjectures` were changed.

## Where the brief, the DAG or earlier work was wrong

Step 2 was labelled elementary but requires an actual larger-index geometric
continuity assertion. The recorded small-index equality lemma cannot be applied
to the original index directly. The new node isolates precisely that step;
the small-index side is already proved using Mathlib.

Searches found Mathlib's `Scheme.preservesColimit_yoneda` and its factorization
and equality constituents, all with the index in the scheme universe. The
coefficient representable-continuity module cannot be used here: its proof
imports `ProEtaleClassicalSheavesImage`, which imports the present item.

The current blueprint's definition and classical-sheaves unit/proof were read,
as were Stacks `proetale.tex` lemma-limit-pullback and `limits.tex`
proposition-characterize-locally-finite-presentation. The unit route is kept.
Edge cases checked in the geometric reduction are constant/singleton diagrams,
the empty affine vertex and zero rings, and parallel arrows: no nonempty
scheme or nonzero ring hypothesis is introduced; cofilteredness supplies only
a nonempty index.

## New nodes

`lem-pe-affine-etale-large-limit-maps` is the larger-index version of the
finite-presentation map factorization/equality argument in parent step 2. It
states preservation only for affine etale representables, not arbitrary sheaves.
It is used to prove finality of the original diagram in the common
costructured-arrow category. The small diagram's finality is proved directly
from Mathlib, and the arbitrary section-cocone comparison is complete Lean.
Its module is `Sheaf.AlgebraicGeometry.AffineEtaleLargeLimitMaps`.
Validation: the new module compiled in 3.9 seconds and the item module compiled
cleanly in 6.9 seconds using lcompile.py. No existing definition or statement was
changed; no change record is needed.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
