## What changed

Proved `AlgebraicGeometry.exists_locallyFiniteType_limit_closed_finitePresentation`
in `Sheaf.AlgebraicGeometry.LocallyFiniteTypeLimitClosedFp`, with its signature unchanged.
Choose a compact open neighborhood of the compact image in the quasi-separated base.
Factor through that qcqs open, apply the existing closed finite-presentation envelope theorem,
and use the concrete `FinitePresentationApproximation.ofIsClosedImmersion` construction.
Its index is the opposite of `i.ker.FGSub`, so zero and sums supply the required nonempty
directed preorder without replacing it by a general cofiltered category. Compose the model
structure maps with the open inclusion, retaining all stage and limit properties.
Updated the node's second proof step to identify the concrete construction used in Lean.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.exists_locallyFiniteType_limit_closed_finitePresentation`
(node `lem-weil-pbc-lft-limit-closed-fp`).
No `sorry` remains in the assigned module. Added 0 holes and split off 0 theorems.
Existing dependencies are used with their existing proofs and statements.
The pruned module compiled in 3.1 seconds. `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` is reachable.

## No longer needed

Removed `public import Sheaf.AlgebraicGeometry.LimitAffineTransition`.
The proof does not use `AlgebraicGeometry.exists_limit_affine_transition` or node
`lem-weil-pbc-limit-affine-transition`: the concrete closed-subscheme approximation
already supplies `A.isLimit`. No other planned proof dependency was pruned: the Nagata
system definitions and property theorem are used, and the morphism permanence nodes are
realized by Mathlib lemmas and instances. No unit statement or unit proof step is bypassed.
This does not assert that `LimitAffineTransition` is globally unused by other modules.

## Where the brief, the DAG or earlier work was wrong

The proof plan is sound. Its Lean interface for `nonempty_finitePresentationApproximation`
uses a general small cofiltered category, whereas this theorem requests a directed preorder.
Using the existing concrete `ofIsClosedImmersion` construction exposes the intended finite-type
subideal index and resolves the mismatch without any statement or definition change.
The empty-source case is covered by the same compact-open-neighborhood theorem, which permits
an empty open, and by the same existing model construction.

Change record: `coord/changes/locally-finite-type-limit-closed-fp-import-pruning.md`.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
