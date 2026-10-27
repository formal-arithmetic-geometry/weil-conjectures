## What changed

Replaced the one proof hole in
`AlgebraicGeometry.Scheme.coefficientConstantTensor_restricted_finite` without changing
its statement or its original public imports. The proof now obtains a bounded K-flat
representative, transports the hypotheses to every intrinsic cohomology object (including
zero ones), applies the existing generic `SheafOfModules.finite_tensor_lisse`, and
transports the resulting finite constant models on every slice back to the conclusion.
The generic predicate comparison is the proved `small_models` helper. Its reuse does not
introduce the finite coefficient-set hypotheses of its containing module's main theorem.

Added `Sheaf.AlgebraicGeometry.CoefficientFixedPullbackExact`, with proved colimit,
finite-limit and additive instances for the actual coefficient-sized fixed-scalar inverse
image. Added `Sheaf.Paper.CoefficientRestrictedTensorFlatModel`, whose theorem is proved:
exactness transports the upper cohomology bound, the existing bounded flat representative
constructs P, and the existing K-flat single-tensor comparison and braiding provide its
tensor model. The remaining geometric compatibility is isolated in
`Sheaf.Paper.CoefficientRestrictedTensorComparison` as an isomorphism in the derived
category, rather than an unrelated collection of per-degree isomorphisms.

All four modules compiled together. The measured individual times were 9.0, 13.7, 22.9,
and 50.5 seconds. A subsequent profile of the main module compiled in 7.0 seconds, with
no slow declaration; profiling options were removed. The final packet is compiled again
by the delivery tool. No shared module, definition, instance, public signature or unit
route was changed. No consumer adaptation is required.

## Proved and sorry left

Original holes: one. The body of
`AlgebraicGeometry.Scheme.coefficientConstantTensor_restricted_finite` is now complete
Lean, conditional on the new comparison. This closes that upper hole by decomposition,
not by an axiom-free proof of the entire obligation.

Added holes: one, exactly
`AlgebraicGeometry.Scheme.coefficient_restricted_tensor_comparison`, node
`lem-sfb-coefficient-restricted-tensor-comparison`. Its body is exactly `:= by sorry`.
There are no other sorry bodies in the packet, no holes inside definitions, and no
arbitrary witness chosen from an unfinished existence theorem in any definition.

The new declarations `coefficientFixedPullback_colimits`,
`coefficientFixedPullback_limits`, and `coefficientFixedPullback_additive` have complete
proofs. The new `coefficient_restricted_tensor_flat_model` has a complete proof from
the named derived comparison and existing proved representative/tensor lemmas. Thus this
is one strict decomposition, with zero net reduction of the hole count (one removed,
one added), and no module withdrawal.

The remaining comparison has neither the original local-finiteness conclusion nor its
local-constancy, Noetherianity, finite-generation or boundedness hypotheses. It only
specializes the existing ringed-topos tensor comparison to the concrete fixed-scalar
coefficient-site inverse image. The actual bounded representative construction and the
entire finiteness argument are outside that remaining hole and are proved here.

## No longer needed

Removed the redundant proof import
`Sheaf.CategoryTheory.CoefficientFixedScalarsLocalModels`; the new model module publicly
supplies the same required scalar-equivalence API. The four original public imports stay.

The original node no longer directly needs its six planned proof dependencies:
`def-weil-pbc-proetale-operations`, `def-sfb-site-derived-constant-module-functor`,
`lem-sfb-constant-scalar-restriction-tensor`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-weil-pbc-locally-constant-tensor`, and `lem-pc-kflat-resolution`.
They are replaced in its direct proof by the bounded model and the two existing generic
helper containers. This is not a claim that all six nodes are globally unnecessary.

Specifically, the original-site operations interface is replaced here by exactness of
the actual coefficient-sized fixed-scalar functor. The constant realization remains a
statement dependency. Scalar monoidality and ringed tensor pullback remain dependencies
of the new derived comparison. The local tensor calculation and flat resolution remain
used through the proved `finite_tensor_lisse` and `bounded_flat_representative` helpers.
No existing Lean module or DAG node is withdrawn or asserted globally prunable.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement was not found false. The planned ringed-topos comparison
has a fully general Lean interface requiring ringed inverse-image data and normalizations;
it cannot be applied directly to `coefficientProEtaleFixedModulePullback` without
constructing and identifying that presentation. That interface specialization is the
remaining named obligation, with a source and a complete proof plan. Unlike the original
finite-local-model statement it asserts only a geometric derived compatibility.

The library already proves the generic finiteness and bounded-flat-representative
lemmas needed here, as private helpers of larger modules. Reusing them removes the need
to reconstruct the local homological calculation or to add any finite coefficient-set
assumptions. The proof preserves the integral-model unit route, the unrestricted module
M in the comparison, zero cohomology, zero coefficients, and empty schemes.

## New nodes

`lem-sfb-coefficient-fixed-pullback-exact`: the proved exact/additive and colimit
preservation interface for the coefficient-sized fixed-scalar inverse image. Its Lean
attachment lists all three instances.

`lem-sfb-coefficient-restricted-tensor-comparison`: the one unfinished derived
isomorphism, obtained by specializing canonical ringed-topos tensor pullback and
constant-scalar transport. It has no finiteness or boundedness assumptions and no
finite-local-model conclusion.

`lem-sfb-coefficient-restricted-tensor-flat-model`: the proved bounded K-flat
representative and constant tensor model, from the preceding comparison. Its proof
constructs the representative using existing bounded flat replacement and uses the
published K-flat single-tensor isomorphism. There are no change records because no
existing definition, statement, or other module is changed.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
