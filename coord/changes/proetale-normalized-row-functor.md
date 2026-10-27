# Normalized hypercover row restriction functor

## Reason

The completed normalized descent proof compiles, but the delivery's combined
compile and axiom probe exceeds 60 seconds. Elaborating and checking the two
large natural-transformation equalities for identity and composite refinements
repeatedly unfolds the section, alternating-coface, extension, and total functors.
The row restriction is therefore expressed as the map of its actual functor.

## Old and new

In `Sheaf.AlgebraicGeometry.ProEtaleNormalizedHypercoverDescent`, the old
`rowRefinementNat` is a natural transformation with `app := rowRefinement` and
naturality supplied by `rowRefinement_naturality`. The new body is
`(rowRestrictionFunctor X R W).map r.op`. The new public functor composes right-op,
precomposition, the coefficient-presheaf functor, alternating cofaces and extension
by zero, exactly as the existing row maps do. Its object map is the existing
`hypercoverSectionRows`; its component maps are definitionally the existing
`rowRefinement`. The naturality proof is propositionally irrelevant, so the old
and new natural transformations are definitionally equal. No existing statement,
attribute, public import or mathematical construction is changed. The coefficient
and signed-total constructions remain verbatim.

## Consumers and node

The assigned module is held by H2. Searching all of `lean/Sheaf` and
`lean/WeilConjectures` for its module name finds no current Lean importers.
The pending DAG parents remain attached and needed; none is withdrawn. Since the
old and new row transformation are definitionally equal and every signature is
retained, no consumer adaptation is necessary. The new functor is attached to the
assigned existing node. No source-library module is changed, and no target
statement or definition meaning changes.

Two additional proved public lemmas cache the existing `HasSheafify` and
`WEqualsLocallyBijective` propositions, registered only as local instances. This
avoids recomputing the essentially-small-site transport when elaborating the
module's many abelian-category applications. They add no data or assumptions.
