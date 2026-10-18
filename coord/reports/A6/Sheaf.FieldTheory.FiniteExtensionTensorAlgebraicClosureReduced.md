## What changed

Proved `Algebra.finiteExtension_tensor_algebraicClosure_reduced_isSeparable` in
`Sheaf.FieldTheory.FiniteExtensionTensorAlgebraicClosureReduced`, with its existing signature
and docstring unchanged. The proof follows the existing DAG plan: convert finite dimensionality
to `FieldExtension.degree k K ≠ ⊤`, obtain an inseparable element under the negation of
separability, and contradict reducedness using the existing tensor-nilpotent theorem.
Both existing proof imports are used. No definitions or interfaces changed.

Validation: the module compiles using `lcompile.py`, without warnings or errors.
LeanFinder returned separability criteria involving formally unramified extensions, not this
reducedness criterion; Loogle returned no match. Source searches found no shorter existing proof.

## Proved and sorry left

Closed the one local hole:
`Algebra.finiteExtension_tensor_algebraicClosure_reduced_isSeparable`
(node `lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable`).
Proved 1 of 1 original sorries; added 0 holes; split off 0 statements.
No sorry remains in the delivered module.

The proof uses the already stated dependencies
`FieldExtension.exists_not_isSeparable_of_not_isSeparableExtension` and
`FieldTheory.inseparable_tensorProduct_algebraicClosure_not_isReduced`.
Their existing proofs remain obligations of their own modules; this delivery does not close
those dependencies or claim that the resulting theorem is independent of their sorries.

## No longer needed

None. Both declared proof dependencies and their imports are used; the route and DAG remain
unchanged. No nodes or modules are pruned. Existing public imports retain the statement interface.

## Where the brief, the DAG or earlier work was wrong

None. The finite-degree API uses `WithTop ℕ`, so a small explicit simplification of
`FieldExtension.degree` bridges the `FiniteDimensional` hypothesis to the first dependency.
The existing unit route is preserved, and no new nodes or change records are needed.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
