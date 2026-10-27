## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.space_atlas_open_refinement_pullback` in
`Sheaf.AlgebraicGeometry.SpaceAtlasOpenRefinementPullback`, preserving its complete
statement, universes, binders and public imports.

The key private helper proves that arbitrary small scheme coproducts commute with
pullbacks. Inside the ordinary scheme pullback `P ×_V (∐ U_i)`, the component
pullbacks are disjoint open immersions and cover it. Mathlib's
`nonempty_isColimit_cofanMk_of` gives their coproduct universal property; preservation
of coproducts and reflection of isomorphisms by `Over.forget S` identify the actual
canonical comparison as an isomorphism. Yoneda and pullback pasting give the exact
prescribed presheaf square without gluing sections of the algebraic space.

Private proved helpers also transport scheme-test properties across the unique
representing isomorphism, apply source-local properties to coproducts, and establish
point surjectivity using residue fields. The property-transport and point arguments
reuse the existing private proof patterns from `SpaceEtaleSourceAtlasDetection` and
`AlgebraicSpaceFlatLfpUniversallyOpen`; those private declarations cannot be imported.
The affine covering is constructed from the affine-open basis twice, indexed by the
points of V, with the actual structural factorization supplied by `resLE`.

Updated the assigned node's proof, proof dependencies and proof origin to follow this
argument. Removed the obsolete fppf-covering tool-use approval. No shared module,
definition, public signature or node statement changed; no consumer adaptation or
change record is needed. The unit's route is preserved: this node is a refinement
input below the unit's own statement and steps, not a replacement for them.

Validation: the completed module compiled without errors or warnings in 8.1 seconds,
then in 9.0 seconds after pruning proof imports. All Lean lines have at most 100
characters. Empty index types, empty atlas schemes, repeated opens and arbitrary
small index universes are covered by the proof: no nonemptiness or finiteness
hypothesis was introduced. The affine family of an empty V is indexed by its empty
point type. No arbitrary data are selected from an unproved existence theorem.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.AlgebraicSpace.space_atlas_open_refinement_pullback`
(node `lem-a1-space-atlas-open-refinement-pullback`).

Holes added: 0. Sorries remaining in the item or elsewhere in the delivery: 0.
All private helpers, including the coproduct colimit construction, are complete.

## No longer needed

Removed private imports:

- `Mathlib.AlgebraicGeometry.Sites.Fpqc`;
- `Mathlib.AlgebraicGeometry.Morphisms.Basic`;
- `Mathlib.AlgebraicGeometry.Restrict`;
- `Mathlib.AlgebraicGeometry.ResidueField`;
- `Mathlib.AlgebraicGeometry.Pullbacks`;
- `Mathlib.AlgebraicGeometry.Gluing`.

The needed source-locality, restriction and residue-field API is already available
through the unchanged public imports. `Mathlib.AlgebraicGeometry.PullbackCarrier`
remains a proof import for scheme point lifting.

Removed proof dependencies:

- `lem-pc-zariski-coverings-are-fppf`: equality of sections of E need not be checked
  on a cover; the representing square is obtained by pasting scheme pullbacks.
- `lem-weil-pbc-scheme-morphism-gluing`: the scheme coproduct comparison follows
  from disjoint open components and the existing coproduct characterization.
- `lem-weil-pbc-open-fibre-product`: the larger restriction square is unnecessary;
  the direct open-immersion base-change lemma suffices.

The obsolete top-level tool-use entry
`lem-pc-zariski-coverings-are-fppf` was removed. All statement dependencies stay.
The replacement proof cites the existing Mathlib leaves
`lem-weil-pbc-open-immersion-base-change` and
`lem-weil-pbc-scheme-pullback-compatible-point`. No project module is withdrawn;
the removed dependencies may still be needed by other parents.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The DAG's original section-gluing
argument was valid but longer than necessary: one can construct the coproduct
pullback comparison in schemes and then paste with the given representing square.
The existing theorem docstring retains that valid alternative natural-language proof;
the updated node records the Lean implementation's shorter route.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
