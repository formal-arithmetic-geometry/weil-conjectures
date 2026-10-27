## What changed

Proved `WeilConjectures.PodCoefficientDescent.integral_comparison_existsUnique` in
`Sheaf.Paper.PodReindexingHomCoefficientDescent`. The comparison is the prescribed
kappa conjugate of the ambient comparison. Completion-unit invertibility follows
from constructible completeness and the existing legacy-completeness equivalence;
naturality follows from the ambient reindexing law and kappa naturality. Cancellation
proves normalization and uniqueness. Added the private proof import
`Sheaf.Paper.SfDerivedCompleteLegacyComparison` and two proved private helpers.
Public signatures, definitions, and public imports are unchanged.

## Proved and sorry left

Closed one of the 23 holes present at dispatch:
`WeilConjectures.PodCoefficientDescent.integral_comparison_existsUnique`.
Added zero holes and split off zero statements. The nine obligations already proved
in the shared module are retained and are not counted as new work.

The following 22 declarations retain their original `sorry`, all attached to
`lem-pod-reindexing-hom-coefficient-descent`:

- `WeilConjectures.PodCoefficientDescent.ambient_reindex_scalar`
- `WeilConjectures.PodCoefficientDescent.ambient_scalar_chain`
- `WeilConjectures.PodCoefficientDescent.ambient_coordinates`
- `WeilConjectures.PodCoefficientDescent.rational_transpose_existsUnique`
- `WeilConjectures.PodCoefficientDescent.rational_signedShift_existsUnique`
- `WeilConjectures.PodCoefficientDescent.rational_comparison_existsUnique`
- `WeilConjectures.PodCoefficientDescent.integral_existsUnique`
- `WeilConjectures.PodCoefficientDescent.integral_scalar`
- `WeilConjectures.PodCoefficientDescent.rational_scalar`
- `WeilConjectures.PodCoefficientDescent.integral_evaluation_transposition`
- `WeilConjectures.PodCoefficientDescent.rational_evaluation_transposition`
- `WeilConjectures.PodCoefficientDescent.rational_composition`
- `WeilConjectures.PodCoefficientDescent.rational_pullbackShift_existsUnique`
- `WeilConjectures.PodCoefficientDescent.rational_signed_shifts`
- `WeilConjectures.PodCoefficientDescent.common_evaluation_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_pair_permitted`
- `WeilConjectures.PodCoefficientDescent.common_comparison_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_evaluation`
- `WeilConjectures.PodCoefficientDescent.common_transpose_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_transposition`
- `WeilConjectures.PodCoefficientDescent.common_compositor_existsUnique`
- `WeilConjectures.PodCoefficientDescent.common_composition`

## No longer needed

No imports or modules are pruned globally: the remaining obligations still use
their existing proof plan. For the newly proved integral comparison obligation,
the scalar-completion exchange, DVR arithmetic, normalized scalar realization,
and specified scalar-Hom pinning steps are unnecessary. Its hypotheses already
supply law-bearing completion data and the ambient comparison; invertibility and
conjugation suffice. These dependencies remain in the node for the unfinished
scalar compatibility and evaluation obligations.

## Where the brief, the DAG or earlier work was wrong

The detailed scalar construction in the original docstring is more than this
particular existence-and-uniqueness obligation requires. The proof uses the
existing comparison and laws directly. No statement repair is made. A larger
rational-extension draft and a common-stage transposition draft were explored
but are not included in this delivery. They introduced no new statements or holes.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
