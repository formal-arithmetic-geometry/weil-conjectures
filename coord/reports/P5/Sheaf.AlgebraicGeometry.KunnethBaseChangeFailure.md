## What changed

Proved `AlgebraicGeometry.Etale.exists_kunnethBaseChangeFailure_functionField` by converting the unbounded cumulative hypotheses to the degreewise hypotheses required by the existing cyclic failure witness, then applying a named generic-function-field descent interface. Added `Sheaf.AlgebraicGeometry.KunnethUnboundedBridges` and `Sheaf.AlgebraicGeometry.KunnethFunctionFieldDescent`.

## Proved and sorry left

The target theorem `exists_kunnethBaseChangeFailure_functionField` is proved. Two strictly intermediate results remain as named `sorry`s: `cumulative_and_not_universal_of_unbounded` and `exists_functionField_descent_of_algClosedWitness`.

## No longer needed

The change record is `coord/changes/kunneth-base-change-failure.md`. The direct five-step local presheaf construction listed in the original node is not imported by the completed top-level proof. The existing `UniversalBaseChangeFailureDatum` packages the algebraically closed witness, so the lower-level direct construction dependencies are pruned from this route.

## Where the brief, the DAG or earlier work was wrong

The DAG expands the Stacks descent argument into five local presheaf steps, although `UniversalBaseChangeFailureDatum` already packages the full algebraically closed extension witness and the target differs by the final generic-function-field descent. The unbounded predicate also needs an interface relating canonical pullback exchange maps to arbitrary chosen Cartesian squares; that interface was absent from the stated dependencies and is recorded as `cumulative_and_not_universal_of_unbounded`.

## New nodes

`new-kunneth-unbounded-interface` and `new-kunneth-function-field-descent`.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
