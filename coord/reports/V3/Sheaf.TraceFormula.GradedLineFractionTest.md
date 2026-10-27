## What changed

The target module now proves `gradedLineFraction_test` by applying the local comparison
statement and Mathlib's `Scheme.hom_ext_of_forall`. I added
`Sheaf.TraceFormula.GradedLineFractionTestLocal`, whose named local comparison theorem
isolates the basic-open geometric step and remains the single split-off `sorry`.
The target node's proof route and dependencies were updated to record this reduction.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.Modules.gradedLineFraction_test` (one `sorry` closed).
Added one strictly local theorem,
`AlgebraicGeometry.Scheme.Modules.gradedLineFraction_test_local`, with its proof
left as `sorry`; its node is `lem-trf-graded-line-fraction-test-local`.

## No longer needed

The target proof no longer directly uses the previously listed geometric proof
dependencies; they remain the dependencies of the new local node. No imports were
removed from the target module beyond retaining its chart statement import.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the local basic-open comparison and the final global
scheme-morphism extensionality into one theorem. The global step is an elementary
application of `Scheme.hom_ext_of_forall`; the local comparison is now isolated as a
separate named statement for parallel proof.

## New nodes

`lem-trf-graded-line-fraction-test-local` is the local basic-open comparison required
by the target proof. It is stated in
`lean/Sheaf/TraceFormula/GradedLineFractionTestLocal.lean` and recorded in the
corresponding DAG node.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
