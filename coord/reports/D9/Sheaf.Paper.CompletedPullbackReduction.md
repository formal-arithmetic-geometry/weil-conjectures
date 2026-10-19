## What changed

In `Sheaf.Paper.CompletedPullbackReduction`, proved
`AlgebraicGeometry.Scheme.completedReductionModelPushforward_isRightAdjoint`
using the existing Mathlib instance for sheaf-module pushforward, and proved
`AlgebraicGeometry.Scheme.completedReductionOrdinaryRestrictionUnit_exists`.
The latter uses `reductionCoefficientMap_id`, constructs the identity-on-sections
natural isomorphism using `ModuleCat.restrictScalarsId'App`, and proves uniqueness
by extensionality of isomorphisms, natural transformations, sheaf-module maps,
and their section maps. All existing statements and definitions are unchanged.

## Proved and sorry left

Closed two of the seven original holes:

- `AlgebraicGeometry.Scheme.completedReductionModelPushforward_isRightAdjoint`.
- `AlgebraicGeometry.Scheme.completedReductionOrdinaryRestrictionUnit_exists`.

Added zero holes; split off zero statements. Five original holes remain unchanged,
all attached to node `lemma-weil-pbc-completed-pullback-reduction`:

- `AlgebraicGeometry.Scheme.completedReductionOrdinaryComparison_exists`.
- `AlgebraicGeometry.Scheme.completedReductionFiniteEvaluation_exists`.
- `AlgebraicGeometry.Scheme.completedReductionOrdinaryTransition_exists`.
- `AlgebraicGeometry.Scheme.completedReductionTargetTransition_exists`.
- `AlgebraicGeometry.Scheme.completedPullback_reduction`.

The item compiles through `lcompile.py`. The remaining statements retain their
existing source citations and natural-language proofs. The final theorem still
requires the completion and finite-reduction comparisons and their normalized
coherence, and is not claimed as proved by this delivery.

## No longer needed

None. No import was added or removed. The original proof-dependency imports and
node route remain for the five untouched obligations. Neither of the two closed
auxiliary holes introduces an additional proof dependency module.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found in the statements proved here. This
partial delivery closes two auxiliary holes without changing the main route.
The identity comparison works for every scheme and coefficient datum: it needs
no nonempty site, nonzero ring, boundedness, or generator-list hypothesis.


The resumed session retained both proofs and checked their diff against the current
library source: only the two proof bodies differ. The current sandbox compiled
successfully through `lcompile.py` in 10.6 seconds. The required dry run and push
use the unmodified delivery tooling.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
