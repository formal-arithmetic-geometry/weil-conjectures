## What changed

Replaced the coherence-transport hole in
`Sheaf.Paper.RationalProjectionComparisonEquations` with explicit categorical transport
calculations for all four fields. The proof uses one tensor comparison shared across
all compactifications and maps the integral equalities forward; it does not reflect
equalities through localization.

The new module `Sheaf.Paper.RationalProjectionTensorCompatibility` defines the tensor,
support and direct-image endpoint comparisons. Its proved
`WeilConjectures.rationalProjectionTensorFunctorEq` constructs the shared tensor
comparison from the existing object and pure-tensor formulas. Its remaining theorem
isolates the two local proper/open mate squares, without assuming integral coherence
or asserting any of the four rational coherence equations.

The main proof includes the support-comparison naturality calculations for refinement
and proper coincidence, both sides of the projection composition equation, and both
sides of the support pentagon with its original associativity transport. The residue
Tor criterion supplies the integral second-input domain. No existing declaration
signature or public import was changed.

Both modules were checked with `lcompile.py`. The item compiled in 27.8 seconds;
its sole warning was an unused simplification argument, removed before delivery.
The delivery tool rechecks the exact final packet.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.compactSupportProjectionCoherence_rational`
(node `lem-sf-rational-projection-comparison-equations`) by a complete proof from the
new local mate-compatibility statement and the existing declared dependencies.

Added one hole:
`WeilConjectures.rationalProjectionTensorCompatibility`
(node `lem-sf-rational-projection-tensor-compatibility`). It states only the localized
compact-support and proper-counit component squares through the constructed shared
tensor comparison. Its docstring and node give the proper/open transpose argument.
There are zero holes in the item module and one in the added module. This is a
decomposition (one hole closed, one added), not a net hole reduction.

The shared tensor functor equality and every private helper in the item are proved.
No definition contains a hole or chooses data from an unspecified existence result.

## No longer needed

No modules are withdrawn and no original imports are removed. The new local module
imports `ConstructibleProjectionMates` directly; it does not need the coherence
structure module. The original tensor
and tensor-pullback normalization dependencies are retained through the new local
mate node. The item now directly depends on this node, raw rationalization, the
integral residue Tor criterion and the operation-stage comparison data. In particular,
the proof never assumes a full six-functor datum or invokes the projection-formula
theorem.

## Where the brief, the DAG or earlier work was wrong

The original plan did not expose the shared tensor-comparison requirement as a
separate local statement. `SixFunctorExchangeComparison.tensor` is supplied separately
for each exchange square and is not required to be the same family across different
squares. The existing per-square projection comparison therefore does not immediately
supply the shared comparison needed in the composition calculation.

The new tensor comparison is constructed from the prescribed integral/rational tensor
formulas. The remaining local mate comparison is strictly smaller than the item: it
assumes none of the integral equations and asserts none of the rational equations.
The generic transport proofs now implement the rest of the original plan explicitly.

## New nodes

`lem-sf-rational-projection-tensor-compatibility`, in
`dag/nodes/sec-six-functors/`, records the shared tensor construction and the two local
mate squares. Its Lean module is
`Sheaf.Paper.RationalProjectionTensorCompatibility`. Searches covered LeanSearch,
LeanFinder, Loogle, Mathlib, both library roots, the DAG and the current blueprint.
The unit route is unchanged. There are no definition or statement change records.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
