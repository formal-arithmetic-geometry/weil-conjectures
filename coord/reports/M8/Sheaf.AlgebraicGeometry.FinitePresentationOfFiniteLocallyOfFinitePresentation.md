## What changed

Proved `AlgebraicGeometry.finitePresentation_of_finite_of_locallyOfFinitePresentation`
in `Sheaf.AlgebraicGeometry.FinitePresentationOfFiniteLocallyOfFinitePresentation` by
assembling the four conjuncts with `inferInstance`. Mathlib's `IsFinite.toIsAffineHom`
provides affineness, the affine-morphism instance provides quasi-compactness,
`IsSeparated.of_isAffineHom` provides separatedness, and the separated-morphism
instance provides quasi-separatedness. Local finite presentation is the hypothesis.
The theorem signature and visibility are unchanged. The argument follows the existing
node and docstring exactly, so no DAG change is needed.

Removed the redundant proof import `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
The two public imports needed by the statement are retained.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.finitePresentation_of_finite_of_locallyOfFinitePresentation`
(node `lem-trf-finite-morphism-finite-presentation`).
Added 0 holes, split off 0 statements, and left 0 holes in the item module.
The complete module compiles cleanly through `lcompile.py` (2.0 seconds).

## No longer needed

Removed direct import `Mathlib.AlgebraicGeometry.Morphisms.Affine`, which is already
available transitively through the necessary Mathlib imports. Its affine API is still
used by the proof. No DAG nodes or project modules are pruned. All three declared
proof dependencies remain used: `def-weil-finite-integral-morphism` supplies finiteness
and affineness; clause (3) of `lem-weil-pbc-affine-morphism-permanence` supplies
quasi-compactness, separatedness and quasi-separatedness through its Mathlib match;
`def-sbc-locally-finite-presentation` supplies the local-finite-presentation class and
the interpretation of the conjunction as finite presentation. No unit route changes.

## Where the brief, the DAG or earlier work was wrong

None. The existing proof plan is implemented directly by Mathlib instances.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
