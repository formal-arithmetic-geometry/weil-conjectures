## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.point_open_calculus`, including all seven
conjuncts, in the assigned module. Its statement, public imports, and definitions
are unchanged. All supporting lemmas are private and proved.

The proof first proves the common-field relation is an equivalence, using a point
of a scheme pullback and its residue field for transitivity. It then proves
compatible-point lifting for arbitrary presheaf pullback squares, identifies
scheme points with Yoneda point classes, and obtains the scheme-test image formula
and the surjectivity criterion. The existing affine-atlas theorem supplies the
topology comparison and scheme-source continuity/openness. Openness of a general
representable etale map descends from its pullback along a target atlas. Finally,
subfunctor injectivity and surjective open-immersion scheme tests prove the open
embedding, atlas image, order, and full-image clauses.

Updated the item's DAG proof, proof dependencies, and proof origin to this actual
argument. Added the existing Mathlib leaf
`lem-weil-pbc-scheme-pullback-compatible-point` as a proof dependency. No other
existing module or node is changed, and no shared interface needs adaptation.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.AlgebraicSpace.point_open_calculus`
(node `lem-a1-space-point-open-calculus`). Added 0 holes; split off 0 statements.
There are no remaining `sorry` declarations in the delivered module.

The proof uses the already stated
`AlgebraicGeometry.AlgebraicSpace.exists_affine_etale_cover_and_point_topology`;
its existing proof obligation is not changed or duplicated by this delivery.

## No longer needed

Removed the redundant proof imports `Mathlib.AlgebraicGeometry.Morphisms.Etale`
and `Mathlib.AlgebraicGeometry.ResidueField`; their relevant declarations are
already available through the unchanged public imports. Added private proof
imports of `Mathlib.AlgebraicGeometry.PullbackCarrier` and `Mathlib.Data.Quot`.
The private affine-atlas import is used.

The proof does not use the closure or covering theorems of
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`
(node `lem-trf-space-fibre-products-etale-covers`). It uses the ordinary
categorical pullback of sheaves and its preserved presheaf square directly.
Removed that node from `proof_deps` and withdrew its obsolete top-level tool-use
approval. Its original public import and statement dependency are preserved;
this delivery therefore claims no module pruned from the targets' import closure.
All other original proof dependencies are used. No chapter or unit route changes.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The previous plan omitted a formal
proof that the common-extension relation is already an equivalence; the new
private proof supplies it rather than treating equality in a generated quotient
as a single relation step without justification. The original source-atlas
openness argument is replaced by the equivalent target-atlas pullback argument,
which also handles the presheaf underlying an open subfunctor directly.

The proof covers empty source/target and empty open subfunctors without a
nonemptiness assumption. Scheme-point injectivity uses common-field agreement;
scheme-point surjectivity uses the canonical residue-field factorization. The
order criterion is proved objectwise using an actual inverse of each surjective
open immersion, so containment is not inferred from arbitrary point data alone.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
