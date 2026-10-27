## What changed

Partial proof delivery for `Sheaf.Paper.ProjectionTensorCoefficientComparison`.
Prove `WeilConjectures.ProjectionTensorCoefficient.completion_isIso` by comparing
the ordinary tensor presentations on the product good-complex localization and
applying the criterion for the actual canonical completion unit. All existing
public signatures, definitions and public imports are unchanged. The previously
proved `good` is preserved. Added imports are proof-only. Update the existing
node's proof route and dependencies to match the proof. File-local transparency
and instance-priority settings keep the standard localization and tensor
constructions from being unfolded unnecessarily; public attributes stay unchanged.

Validation: the final module compiled cleanly with `lcompile.py` in 58.1 seconds,
exit code 0; profiler options removed. An earlier delivery attempt exceeded the
60-second limit and pushed nothing; the localized elaboration settings and explicit
isomorphism-composition proof repair that performance issue.

## Proved and sorry left

Closed 1 of the item's 4 original holes:

- `WeilConjectures.ProjectionTensorCoefficient.completion_isIso`.

Added 0 holes. Three original holes remain, all attached to
`def-sf-projection-tensor-coefficient-comparison` with their original complete
natural-language proofs and sources:

- `WeilConjectures.ProjectionTensorCoefficient.ordinary_existsUnique`.
- `WeilConjectures.CompactSupportCoefficientTensor.integral_existsUnique`.
- `WeilConjectures.CompactSupportCoefficientTensor.rational_existsUnique`.

No new statements, nodes, axioms or hollow definitions are introduced.

## No longer needed

No existing import, node or module is pruned. The completion argument uses
derived completeness from the existing constructible tensor theorem and the
canonical completion-unit criterion; it needs no additional chain-coordinate
uniqueness lemma. The ordinary, integral and rational normalization obligations remain.
Exploratory proof imports of `TensorPullbackRepresentativeDescent`,
`RingedTopoiCanonicalTensorPullbackOfUniverses`,
`TensorColimitsIndependentCoefficients`, and `Mathlib.CategoryTheory.Limits.HasLimits`
were removed before delivery; none was an existing import of the item.

## Where the brief, the DAG or earlier work was wrong

The old DAG proof covered only the already proved `good` and referred readers to
the four theorem docstrings for everything else. The updated proof records the
newly implemented completion argument and the three unchanged holes explicitly.
The newest unit `sk-rem-sf-pf-done` has no realized statement or steps to bypass;
its route is preserved. The newest projection-formula proof no longer has a
numbered step 13, so the existing source reference is historical.

The generic tool from another unit is `integralOperationsGoodLocalization_isLocalization` in
`lem-pur-integral-operations-well-defined`. It supplies localization of precisely
the existing good-complex class, without changing the unit-level tensor
construction. The Mathlib localization universal property and product localization
are also recorded in the node. No tool-use approval field is edited.

An attempted ordinary comparison used `tensorComparisonDescent`, the exact
coefficient factorization, and the signed-total naturality lemma. Both the descent
argument and cancellation elaborated after explicit instance and tensor-map
normalization, but kernel checking the ordinary proof took 79.5 seconds, over the
per-file limit. That attempted proof and its proof imports are excluded from this
partial delivery; the original theorem and full docstring plan remain intact.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
