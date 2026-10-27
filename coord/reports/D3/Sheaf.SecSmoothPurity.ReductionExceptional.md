## What changed

In `Sheaf.SecSmoothPurity.ReductionExceptional`, prove
`AlgebraicGeometry.ProEtale.reductionEtaleTateExtensionMap_isIso`. The ordinary
scalar transpose is the canonical isomorphism obtained by composing the scalar
adjunctions from Z/N and applying uniqueness of left adjoints. Its root-generator
formula identifies it with the existing normalized map. The source Tate line is
flat by its etale rank-one trivializations. Its degree-zero complex is K-flat,
so the derived scalar comparison is invertible as well. The N=0 case is treated
on the empty scheme; no flatness of the coefficient homomorphism is assumed.

Factor `reductionEtaleTateExtensionMap` through the existing
`purityScalarSingleMap`, followed by the single of the ordinary scalar transpose.
The private generic theorem `reductionFactoredTranspose` identifies this composite
with the old transpose by adjunction naturality and naturality of the exact-single
comparison. This is a definition performance repair, with unchanged public
signature and unchanged mathematical map. The explicit concrete specialization
was separately checked by Lean. The change record is
`coord/changes/reduction-etale-tate-extension-factorization.md`.

Add public import `Sheaf.Paper.VectorPurityScalarSingle` for that definition and
private proof import `Sheaf.Paper.ScalarPullbackIsoUniqueness`. Import all of the
already imported `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine` to use its proved
rank-one local trivializations. The scalar-representative helpers used from
`ScalarPullbackIsoUniqueness` are themselves completely proved. All added helpers
in this module are private and proved. No adopted source file changes.

Retain all six main exceptional-comparison assembly steps in the node, and add
the Tate normalization argument and its actual dependencies. The main theorem
remains open, so its geometric route and dependencies are retained.

## Proved and sorry left

Original holes: 2. Closed: 1. Added: 0. Split off: 0.

Closed: `AlgebraicGeometry.ProEtale.reductionEtaleTateExtensionMap_isIso`
(node `det-sp-reduction-exceptional`).

Remaining: `AlgebraicGeometry.ProEtale.reductionExceptional_isIso`
(node `det-sp-reduction-exceptional`), with its original statement and proof
in words. This is the sole remaining sorry in the delivered module.

The final module first compiled cleanly in 51.3 seconds. The concrete equality with
the old transpose compiled separately in 29.6 seconds. A scratch package compiled
the repaired module and the unchanged direct consumer
`Sheaf.SecSmoothPurity.PurityDncCoefficientTransport` together, successfully, in
96.6 and 75.1 seconds respectively under the loaded server. The unchanged
`Sheaf.Paper.RawChartScalarCounitPasting` then compiled in 5.3 seconds with that
scratch package's compiled modules explicitly available. No consumer source
adaptation was needed. The delivery preflight supplies the required packet
validation.

## No longer needed

None. No modules, nodes or original imports are pruned. In particular the
unfinished exceptional comparison still needs its six-step geometric assembly;
proving the Tate comparison does not withdraw any of those obligations.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is disputed. The original concrete adjunction formula
caused repeated 60-second timeouts when combined with the new proof. Profiling
isolated substantial kernel work in its definition. The existing generic
scalar-single interface gives the same map while keeping its functor endpoints
shared; the generic transpose identity verifies the factorization. The
ordinary/derived Tate comparison needed this interface repair to fit the file's
compile limit. The current rework archive is preserved; the restored item and
its Lean attachment are retained.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
