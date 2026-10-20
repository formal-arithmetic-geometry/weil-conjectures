## What changed

Proved the abstract mate transport identity by extracting the complete tensor-square mate calculation into `CategoryTheory.projectionMate_square_of_tensor_coherence_projection`. Added the concrete pro-etale tensor coherence interface and wired the target module to the abstract route.

## Proved and sorry left

Closed `CategoryTheory.projectionMate_square_of_tensor_coherence_projection`. The target `AlgebraicGeometry.Scheme.proEtaleProjectionFormula_baseChange` remains open, and `AlgebraicGeometry.Scheme.proEtaleProjectionFormula_tensor_coherence` is split off as an independent lower theorem.

## No longer needed

Removed the curried comparison-compatible route and its `ProjectionMapMate` import; the proof route uses the tensor-square mate theorem directly.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the explicit conversion between uncurried tensor comparisons and the curried projection-map API. The abstract helper records this conversion separately.

## New nodes

- `lem-weil-pbc-projection-mate-square-coherence`
- `lem-weil-pbc-proetale-projection-formula-tensor-coherence`

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
