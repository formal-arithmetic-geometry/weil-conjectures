## What changed

Filled `AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_successor`
from the existing `AlgebraicGeometry.Etale.ordinaryAffineCounit_tensor_normalization`.
The public statement and its source, counit, trace and coefficient definitions stay
unchanged. Added proof imports of OrdinaryAffineCounitTensorNormalization and
AffineTraceCompactComparisonRestriction, with private proof imports exposing the
compactification and colimit definitions needed for comparison elaboration.
The canonical source-descent comparison is proved in the new module
AffineOrderedCounitDescentComparison. Its auxiliary lemmas and all other comparison
and transport lemmas are private and proved. The extraction keeps the files within
the 60-second compilation limit after local opacity and explicit categorical
calculations removed unnecessary unfolding; it adds no holes.

The comparison proof identifies the two source-descent recursions, identifies the
bounded and unbounded tower compact-support comparisons, and transports the known
normalization across the explicit coefficient isomorphism
`coefficientComparison.symm ≪≫ towerTateIso`. Projection naturality and cancellation
then recover the required equation. This works at every rank, so the supplied
preceding-rank hypothesis is unnecessary.

The existing normalization and restriction nodes from `sk-prop-an` are used as tools:
they state the ordinary ordered affine integration calculation itself, not a different
purity route. The diagonal/DNC/vector-bundle unit route is preserved. No shared
interface, existing definition, target statement or other module is changed.

Searches run through msearch: Lean Finder for coefficient linearity of a composite
adjunction; Loogle for `CategoryTheory.Adjunction.comp_counit_app`; Mathlib grep for
`counit.*tensor|tensor.*counit`. These returned generic adjunction/monoidal identities.
A project search found the existing all-ranks normalization, which supplies the shorter
route used here.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.ordinary_counit_successor`
(node `lem-pur-affine-ordered-counit-successor`). One of one holes closed; zero holes
left in the item; zero holes added; zero split-off unproved statements. One proved
comparison was extracted into a new module for compile time. The existing
normalization theorem retains its own already-stated dependencies; their proofs are
not claimed here.

## No longer needed

No original import was removed, and no module is withdrawn. The old direct proof route
through `def-weil-pbc-composite-adjunction`, `lem-pur-composite-integration-counit`,
`lem-pur-finite-projection-action-laws`, `lem-asd-ordinary-finite-p1-adjunction`,
`lem-asd-etale-finite-twist-pullback` and `lem-amb-affine-space-top-trace` is not repeated
in this item's proof. Those nodes are no longer direct proof dependencies here;
several remain transitively required by the unchanged data or reused normalization.
`lem-amb-shriek-tensor-composition` remains for the actual projection construction.
No whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

The original plan overlooked the already-stated all-ranks ordinary affine counit tensor
normalization. Its coefficient model and left/source comparisons differ syntactically
from this item's model, but the private comparison proofs identify their specified
maps. Reusing it avoids a second geometric coefficient-counit induction. The named
`compositeIntegrationCounit` interface also requires separated finite-type k-schemes,
whereas this item assumes only a Noetherian base with a map to Spec k. The reused
ordinary normalization has exactly the generality needed here.

## New nodes

`lem-pur-affine-ordered-counit-descent-comparison`, realized by the proved theorem
`AlgebraicGeometry.ProEtale.AffineOrderedIntegration.normalized_source_descent` in
`Sheaf.Paper.AffineOrderedCounitDescentComparison`. This identifies the two canonical
source recursions; it is strictly the source-comparison part of the argument and does
not assert any counit or trace equation. The new module has zero holes.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
