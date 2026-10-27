## What changed

Proved `WeilConjectures.PodConstructibleMate.fiberModels_isPullback` in
`Sheaf.Paper.ConstructibleWeilModelSquares`. The underlying scheme square lifts to an
`IsPullback` in `Over (Spec k₀)` by `IsPullback.of_map_of_faithful`. The right-adjoint
`Over.pullback` preserves that pullback; the geometric over-category forgetful functor
preserves connected limits and therefore preserves the resulting pullback.

This implements the existing declaration's documented proof without changing any
signature, definition, public import, or DAG route. Single-file compilation passed,
including after removing all three trial proof imports: the original public imports
already expose the required Mathlib API. The delivery preflight checks axioms separately.

## Proved and sorry left

Closed 1 of 1 holes:
`WeilConjectures.PodConstructibleMate.fiberModels_isPullback`
(blueprint: `def-pod-constructible-weil-model-squares`).

Holes added: 0. Split off: 0. Remaining holes in the delivered module: 0.

## No longer needed

None. Both original public imports are retained for the existing statements and
constructions. No declared dependency, node, or module is pruned. Temporary explicit
Mathlib imports for connected over-category limits, adjunction limits and the
`IsPullback` functor API were unnecessary and are absent from the delivered file.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The existing docstring's categorical proof
works without any separatedness assumption or extra geometric lemma. The definition
node has no numbered proof steps or proof dependencies; its statement and attachment
remain unchanged.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
