## What changed

Replaced the proof of
`AlgebraicGeometry.AlgebraicSpace.exists_atlas_point_comparison` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceAtlasPointComparison`.
The statement and all public imports are unchanged. The proof follows the existing
five-step route: represent the common fibre product, transfer the étale and surjective
properties from the scheme tests, lift pairs of points, prove the two subset identities,
and deduce the equivalence of openness.

Added proof-only imports of `Mathlib.AlgebraicGeometry.PullbackCarrier` for field
amalgamation through scheme pullbacks and `Mathlib.Logic.Relation` for the generated
equivalence relation of `Quot`.

Added proved private helpers for the common-field relation's equivalence property,
functoriality of `schemePointMap`, converting equality of point classes into common-field
maps, and transferring representable properties to an arbitrary representing square.
Transitivity uses Mathlib's scheme pullback point theorem and the residue field of a
point of the pullback. The DAG proof now records these details and the actual order of
the construction. No shared interface, definition, or other existing module changes.

Validation: the final item compiled successfully through `lcompile.py` in 4.6 seconds,
with no errors or warnings. The existing theorem signature is unchanged, all lines
are at most 100 characters, and the DAG proof dependencies equal the union of its
steps' dependencies.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.AlgebraicSpace.exists_atlas_point_comparison`
(node `lem-a1-space-atlas-point-comparison`).
There are zero holes left in the item and zero holes added elsewhere; no split-off
statements. All four private helper theorems have complete proofs.

## No longer needed

None of the original imports or declared proof dependencies is pruned. Each of
`def-trf-algebraic-space`, `def-pc-scheme`,
`lem-weil-pbc-etale-morphism-open-map`, `lem-a1-space-fibre-product-point`, and
`def-a1-algebraic-space-point-classes` is used by the proof. No modules are withdrawn,
and the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

The old step 3 described the fibre-product lemma's point hypothesis as exactly equality
of point classes. Its Lean statement instead requires explicit maps from a common field.
The point-class definition uses `Quot`, hence its generated equivalence relation. The
proof bridges this difference by proving the common-field relation reflexive, symmetric,
and transitive, then extracting a common-field witness and composing its maps with the
canonical residue-field maps. No statement repair is needed.

The edge cases cause no additional hypotheses: empty atlases or target give vacuous pair
lifting, and the subset identities work for both the empty and universal subsets. In the
transitivity argument only the spectra of fields require points; the construction uses
their canonical closed points. Lifts need not be unique.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
