## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.exists_scheme_fibreProduct_point` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductPoint`, with its statement unchanged.
Convert the given representable-diagonal property to Mathlib's relative
representability predicate, apply `Functor.relativelyRepresentable.of_diag`, and
use Yoneda fullness to obtain the scheme projections and their pullback square.
Evaluate that square at the common field spectrum, lift the compatible pair of
maps with `Types.exists_of_isPullback`, and evaluate the resulting scheme map at
the supplied point. The surjectivity conclusion follows by applying this lift
for each point of C.

Added private proof imports of Mathlib's relative representability, products in
Over, and pullbacks in Types. Updated the existing node's proof, proof_deps and
proof_origin to match this implementation. No declarations or definitions changed. The public import pruning is recorded in
`coord/changes/h2-algebraic-space-fibre-product-point-import.md`.

Validation: the server compiled the proof cleanly, including after removing the
unused joint-surjectivity import. `#print axioms` returned exactly `propext`,
`Classical.choice`, and `Quot.sound`. All new Lean lines are at most 100 characters.
The empty-source cases remain valid: the lifting clauses use their hypotheses
only, and the final pointwise surjectivity proof has no nonemptiness assumption.
The unit record has no realized statement or steps assigned to this node; the
representable-diagonal and common-field route remains the source's route.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_fibreProduct_point`
(node `lem-a1-space-fibre-product-point`). No sorry remains in the module.
No holes added; no statements split off. This proof depends on no sorry axioms.

## No longer needed

Removed `public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`.
The node `def-trf-algebraic-space-jointly-surjective-family` is unnecessary as a
proof dependency because the theorem's hypothesis already expands the common-field
condition. It remains a statement dependency explaining that condition. Its module
has other consumers and is not withdrawn. The downstream use of
`IsJointlySurjective` is in `AlgebraicSpaceAffineAtlasOpenCover`, which already
publicly imports the defining module itself; no consumer adaptation is required.

Removed the old proof import
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the new proof imports
already provide the needed pullback API. No other DAG nodes or modules are pruned.
A trial import of `Mathlib.CategoryTheory.Limits.Preserves.Yoneda` was unnecessary
and was removed before delivery.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's second step describes extending two field
representatives; the actual Lean statement already provides their common field,
the compatible maps, and the point. Accordingly the proof lifts those data directly.
Mathlib's `Functor.relativelyRepresentable.of_diag`, found by LeanFinder, implements
the first step without new intermediate theory. Searches also included Loogle for
`CategoryTheory.IsPullback.lift`, the msearch grep for representable diagonals and
Yoneda pullbacks, and local searches through Mathlib, WeilConjectures and Sheaf.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
