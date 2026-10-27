## What changed

Filled `AlgebraicGeometry.affine_split_morphism_positive_rank_pieces`, with its signature
unchanged. The proof obtains the existing rank strata from
`finiteLocallyFree_fiberDimension_isLocallyConstant`. The section supplies a point of every
fibre, so its global sections are nontrivial and `Module.finrank_pos` excludes rank zero.
Clopen-idempotent correspondence and `IsAffineOpen.Spec_basicOpen` provide both affine
pieces. Local constancy on the compact affine target gives a finite range, and
`nonempty_isColimit_cofanMk_of` identifies the disjoint covering open inclusions as the
required coproduct. The empty-target conclusion is proved directly.

Updated the item's node proof and proof origin to describe the Lean argument. No other
existing module, statement, definition, or public import changed. No new declarations or
nodes were introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.affine_split_morphism_positive_rank_pieces`
(node `lem-a1-affine-split-morphism-positive-rank-pieces`).

The delivered item has zero `sorry`s. Zero holes added; zero statements split off.
The proof uses the existing, proved fibre-degree decomposition and Mathlib lemmas.

## No longer needed

Removed the proof imports `Mathlib.AlgebraicGeometry.OpenImmersion` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`. Their required basic infrastructure
already comes through the existing public imports, and the proof uses no separate
quasi-separatedness result. The localization-to-affine-open argument is encapsulated by
`IsAffineOpen.Spec_basicOpen`; the finite-subcover argument is encapsulated by
`IsLocallyConstant.range_finite`. These still implement the corresponding existing DAG
steps, so no dependency node or module is withdrawn. All public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned explicit retraction on fibre global sections is
unnecessary: a section gives a point in each fibre, and the existing nontriviality instance
for sections over a nonempty open plus finite-dimensionality proves positivity directly.
Mathlib also already supplies the finite-range and disjoint-open coproduct arguments.
The unit route is unchanged.

Edge cases: the empty target makes positivity vacuous and forces the index set empty;
empty rank strata still correspond to basic opens and are affine; rank zero is excluded
pointwise without assuming the target itself nonempty. Identity maps and targets with
mixed positive ranks use the same proof.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
