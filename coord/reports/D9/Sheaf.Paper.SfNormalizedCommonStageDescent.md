## What changed

Replaced the proof of `WeilConjectures.sfNormalizedRecollement_commonStage_descent`
with an explicit descent through the existing `StageSystem.Morphism` quotient.
The theorem's statement, public imports, and all definitions are unchanged.
Three proof imports supply the scalar comparisons, the already proved normalized
rational triangle/orthogonality theorem, and the native StageSystem functor API.

The proof constructs the two stage-system endomorphisms and compatible unit/counit
families, descends their natural transformations, and verifies both normalization
squares and literal object formulas. It then transports the finite-stage triangle
through the exact inclusion, writing the connecting arrow and its triangle
isomorphism explicitly. For orthogonality, it conjugates every common-stage raw Hom
by the scalar and shift comparisons to a zero finite-stage Hom. Quotient induction,
`isoToStage`, and additivity of the inclusion show that each represented arrow is zero.
This argument avoids assuming that an original-field inclusion is full.

Added `Sheaf.Paper.SfNormalizedRecollementScalarCoherence` for precisely the first
step of the original plan: scalar comparison isomorphisms, their tower equations,
and their compatibility with the two specified maps. This finite-stage statement
contains no descended presentation, no triangle assertion, and no Hom vanishing.
It is strictly a part of the argument; the remaining quotient construction and
both consequences are proved in the assigned module.

## Proved and sorry left

Closed the body hole of
`WeilConjectures.sfNormalizedRecollement_commonStage_descent`
(node `lem-sf-normalized-recollement-common-stage-descent`). The assigned module
has zero remaining holes.

Added one named hole:
`WeilConjectures.sfNormalizedRecollement_scalar_coherence`
(node `lem-sf-normalized-recollement-scalar-coherence`), in its own module with
a source and proof in words. This is a decomposition: one hole closed and one
strictly smaller hole added, net zero, rather than a complete proof of the original
obligation from already available declarations. Existing dependencies retain their
own independently assigned holes.

## No longer needed

No modules withdrawn and no existing imports removed. Global pruning: none.

The parent's direct dependencies `lem-fix-operation-reduction`,
`def-weil-rationalization-karoubi`, and `lem-weil-scalar-extension-composition`
are used by the new finite-stage coherence lemma, rather than by the quotient
argument. They remain needed, and are not claimed as globally pruned.
The parent also no longer cites `lem-weil-scalar-extension-exact-triangulated`
directly: its use is encapsulated by the exact stage inclusions already exposed by
`def-weil-algebraically-closed-coefficients`. No adopted source declaration changes.

## Where the brief, the DAG or earlier work was wrong

No statement correction or source error. The original plan's first step requires
coherent scalar comparisons of the supplied normalized presentations. The generic
pair-functor descent declaration requires these comparisons as input and does not
construct them from the integral/rational normalization hypothesis. The new lemma
isolates exactly that missing input; the remaining original steps are implemented.

The finite-stage coherence statement was checked against identity coefficient
extensions, zero objects, empty open or closed complements, arbitrary base fields,
and distinct input coefficient fields. Its tower and map equations have the same
orientations as `StageSystem.Morphism.coh` and `StageSystem.Morphism.Hom.comm`.
The quotient proof uses all signed shifts and independently chosen source and target
objects, as required by the original statement. The unit route is unchanged.

## New nodes

`lem-sf-normalized-recollement-scalar-coherence` is the finite coefficient comparison
step of `lem-sf-normalized-recollement-common-stage-descent`, with source in the
current blueprint's triangle and Hom-vanishing paragraphs. Searches used LeanSearch,
LeanFinder, Loogle, Mathlib grep, project grep, and the complete blueprint index.
No existing declaration gives these comparisons for the supplied presentations.
The new node retains the original coefficient-theory dependencies. The parent node's
proof and proof dependencies now describe the Lean quotient descent and transport.
No definition or statement was changed; no change record is required.

Validation: the scalar-coherence module compiled on the project server, and the
assigned module compiled successfully in 13.8 seconds after the interface fixes.
The assigned theorem's declaration type was compared verbatim with the source and
is unchanged. Both Lean files satisfy the 100-character line limit.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
