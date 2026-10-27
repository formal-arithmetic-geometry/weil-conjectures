## What changed

Filled `AlgebraicGeometry.Scheme.Modules.invertible_fp_tensor_models` in
`Sheaf.AlgebraicGeometry.InvertibleFpTensorModels`, preserving its signature and public
imports. Added the private proof import
`Sheaf.AlgebraicGeometry.Modules.FinitePresentationTensorProduct`.

The proof follows the four existing DAG steps. The upstream dual instances provide
invertibility and the actual evaluation isomorphism. The existing comparison between
scheme invertibility and sheaf invertibility gives finite local freeness, hence finite
presentation. Apply the object clause of `finitePresentation_descent_affineLimit` twice,
choose a common upper bound, and pull both models to that stage. The existing pullback
preservation theorem gives finite presentation of the models; the canonical
`affineLimitTensorPullbackComparison` composes with their descent isomorphisms to give
`a` and `b`. Tensor permanence and the unit's invertibility give the remaining finite
presentations. Isomorphism instances prove the specified evaluation composite invertible.

The proof uses exactly the declared dependency route, so the node needs no route update.
The theorem has a scoped heartbeat allowance of 800000 because elaboration of the explicit
iterated tensor pullbacks exceeds the default 200000. The complete proof compiled in
13.1 seconds before adding the explanatory linter comment, below the 60-second limit.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.invertible_fp_tensor_models`
(node `lem-trf-invertible-fp-tensor-models`). No holes remain in the item. No holes added,
and no statements split off.

This is a proof from the declared dependencies, including the existing unfinished
`finitePresentation_descent_affineLimit` and `isFinitePresentation_tensorProduct`.
It does not claim those dependencies have been proved here.

## No longer needed

None. No imports, nodes, modules, or approved tool uses were removed. Every declared
proof dependency remains used. No unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The source node's four steps agree with the implementation.
The existing source `Modules.Dual` supplies the dual and evaluation facts through its
instances; finite presentation uses the existing locally free API. No new construction,
statement, definition repair, or consumer adaptation was necessary.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
