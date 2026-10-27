## What changed

Proved `AlgebraicGeometry.projectiveBundle_finiteType_relativeAmple` with its original
signature. Properness gives local finite type and quasi-compactness. Choose the actual
pulled-back tautological quotient along the closed immersion, use the existing
homogeneous-fraction-map theorem to construct its everywhere-generated graded map, and
use the existing inverse-chart theorem to identify that map with the closed immersion.
The existing graded immersion criterion then gives the required affine restrictions.

Added proof imports of `Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap` and
`Sheaf.AlgebraicGeometry.LineQuotientChartInversePullback`. Updated the existing node's
proof and proof dependencies to record these precise applications. No definitions,
statements, public imports, or source-library files changed. The inherited unit route
is preserved: this implements the same projective-to-relatively-ample input.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.projectiveBundle_finiteType_relativeAmple`
(node `lem-sfb-projective-bundle-relative-ample`). Added 0 holes; split off 0 statements.
No sorry remains in the delivered module. The proof uses existing declared results
whose own proofs remain separate stage-3 work; it does not claim they are closed.

The server compiled the proof in 5.0 seconds. The proof does not assume a nonempty
source, locally free E, or a quasi-compact base; its existing input theorems cover empty
schemes, E=0, non-locally-free E, and arbitrary base schemes.

## No longer needed

Removed three redundant private imports: `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`,
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, and
`Mathlib.AlgebraicGeometry.Morphisms.Proper`. The first two are already public imports
of the projective-bundle predicate, and properness is already public from the properness
lemma. Their mathematical notions remain used; no such modules are withdrawn.

The direct proof dependency and existing tool approval for
`lem-weil-pbc-invertible-pullback-invertible` are removed: the inverse-chart theorem
already supplies invertibility of the actual tensor pullback. That underlying result
remains needed transitively, so no global pruning of its module is claimed.
No modules or statements are withdrawn, and no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old plan identifies the quotient's canonical map mathematically, but the Lean
quotient-geometry theorem exposes a different `IsCanonicalMap` predicate from the
one required by the graded immersion criterion. Two already-stated lemmas resolve
this interface gap: the homogeneous-fraction-map theorem constructs the required
`RelativeGradedLineMap`, and the inverse-chart theorem identifies its map with i.
No replacement assumptions or new nodes are needed. The existing declaration docstring
is retained; the node now records the exact Lean argument.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
