## What changed

Proved `AlgebraicGeometry.Scheme.completedSourceAugmentationNormalization` with its
statement unchanged. The strict augmentation identity already specialized in
`CompletedDirectImageLimits.reduction_augmentation` gives the first clause after
functoriality of Rlim and cancellation of the constant/pullback comparison. The
second clause unfolds the specified source realization and cancels the reduction
comparison. Naturality of the actual completion-unit natural transformation gives
the third clause. The first clause of `strictTowerExchangeMateNormalization`,
functoriality and these equations give the fourth clause.

Added a private `import all Sheaf.Paper.CompletedDirectImageLimits` to access its
proved private augmentation lemma. Updated the node proof and proof dependencies
to record this specialization. No declaration signatures, definitions, public
imports or target statements change. A proof-local transparency setting supports the
existing definitionally equal derived-category and tower-corner presentations.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.Scheme.completedSourceAugmentationNormalization`
(node `lem-weil-pbc-completed-source-augmentation-normalization`).

The item has zero remaining holes. Added zero holes and split off zero statements.
This is a complete proof from the existing library declarations; their transitive
unproved dependencies remain assigned to their own modules.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`. Its canonical coefficient
transport is already incorporated into the specialized reduction comparison.

The proof does not directly need
`lem-weil-pbc-profinite-coefficient-inverse-image` or the generic
`lem-weil-pbc-reduction-pullback-derived-tower`; their direct proof edges are removed.
They remain statement dependencies or dependencies of existing constructions, so
this delivery does not withdraw their modules or claim that they leave the target
closure. Existing public imports are retained as the published statement interface.
No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically applicable, but its first step need not be reconstructed
from the generic reduction theorem: the library already proves the exact strict
augmentation equation needed here in `CompletedDirectImageLimits`. The remaining
steps are functoriality, naturality and cancellation of the specified comparisons.
The unit route and all four original conclusions are retained.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
