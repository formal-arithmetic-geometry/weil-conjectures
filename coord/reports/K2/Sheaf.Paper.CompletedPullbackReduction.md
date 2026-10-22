## What changed

Proved the three outstanding finite-interface existence-and-uniqueness theorems in
`Sheaf.Paper.CompletedPullbackReduction`, preserving every mathematical statement and map.
The inferred return type of `completedReductionPulledModelMap` is written explicitly.
The new public construction `completedReductionCompositeCounitNat` forms the canonical
counit comparison once, and the model map is its component. A `rfl` check against the
entire original expression verifies that the actual map is unchanged.

For `completedReductionOrdinaryComparison_exists`, the completed coefficient structure map
is the integral limit lift from `FourCorners`, checked on all projections. Its invertibility
identifies completed module pullback with exact ring-module pullback. The canonical inverse
restriction/pullback mate supplies the ordinary comparison. Evaluation of the two adjunction
units, scalar linearity and restriction naturality give its full local tensor formula.
Surjectivity of the completion projection reduces uniqueness to quotient-unit tensors.

For `completedReductionFiniteEvaluation_exists`, exactness of completed module pullback
implies exactness on strict towers and invertibility of the universal derived pullback
counit on all complexes. On K-flat coefficient representatives, combine this with the
existing reduction-tower computation, the normalized ordinary comparison, and the finite
scalar-extension and restriction computations. Fully faithful restriction to K-flat
representatives descends the comparison uniquely and reflects invertibility. The descended
component equation is precisely the published normalization predicate.

For `completedReductionOrdinaryTransition_exists`, use the scalar-extension adjunction to
send a quotient tensor to its image under the quotient homomorphism. Compose its pullback
with the canonical restriction/pullback mate. Naturality of the finite constant coefficient
comparison supplies the coefficient square. The generator formula determines the natural
transformation uniquely by the module pullback and scalar-extension adjunctions.
The generic transition retains the existing abstract section-equation predicate; its
specialization uses proved generator equalities, avoiding expansion of concrete coefficient
actions in kernel conversion.

Added private proof imports for these constructions and Mathlib's exact derived-functor and
functor-category limit interfaces. New helpers are private and proved. Reused and moved the
existing descent and finite-model helpers so both finite evaluation and the already proved
derived transition use them. Updated the node's auxiliary proof steps and dependencies.
The main completion argument is unchanged. The shared comparison and explicit return type are recorded
in `coord/changes/completed-pullback-model-map-explicit-type.md`; the only consumer is this
module.

## Proved and sorry left

Closed three of the four original holes:

- `AlgebraicGeometry.Scheme.completedReductionOrdinaryComparison_exists`.
- `AlgebraicGeometry.Scheme.completedReductionFiniteEvaluation_exists`.
- `AlgebraicGeometry.Scheme.completedReductionOrdinaryTransition_exists`.

Added zero holes and split off zero statements. One original hole remains untouched:

- `AlgebraicGeometry.Scheme.completedPullback_reduction`, node
  `lemma-weil-pbc-completed-pullback-reduction`.

The already proved derived transition and equal-index restriction comparison are preserved.
This is a proof from existing declarations, including unfinished dependencies; it does not
assert that the entire target import closure is free of `sorry`.

## No longer needed

No imports, declarations, modules or nodes are withdrawn. For finite evaluation, exactness
of completed coefficient pullback replaces the longer constant/completed K-flat tower
calculation described in its docstring. That route's nodes remain needed by the outstanding
main theorem, so none is globally pruned.

## Where the brief, the DAG or earlier work was wrong

The finite evaluation follows directly from the existing profinite coefficient inverse-image
comparison, exactness and K-flat localization. No statement repair or weakening is needed.

The main theorem's planned imports currently close cycles. Both
`Sheaf.Paper.PulledReductionStrictTowerComparison` and
`Sheaf.Paper.PulledReductionNormalizationComparison` already reach this module through
`PbcQbarCompletedPullback`, `PbcConstructibleReductionPullback` and `SbcCompletedOperations`.
`Sheaf.Paper.DerivedFiniteQuotientCoherence` directly imports this module. The import-direction
tool rejects importing each of these from the assigned module. They are held by other groups;
this packet makes no changes to them. The original main theorem and its proof plan remain.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
