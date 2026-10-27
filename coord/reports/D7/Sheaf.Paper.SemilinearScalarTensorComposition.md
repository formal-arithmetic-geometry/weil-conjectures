## What changed

Filled `WeilConjectures.SemilinearSections.scalarTensor_composition` in
`Sheaf.Paper.SemilinearScalarTensorComposition` without changing its signature.
The proof uses the existing `tensor_reduction_formula` and
`semilinearSingletonEvaluationMate_isIso`. A proved private helper transports
singleton derived extension to a left adjoint of the specified evaluation.
A second proved private helper precomposes tensor/reduction compatibility by
two arbitrary maps into evaluated systems.

For the main proof, extend both inputs from level s by this left adjoint.
Postcompose with the tensor of their invertible singleton mates. Naturality,
tensor/reduction compatibility at k and h, and `A.reduction_cocycle` identify
the successive path with the direct path. Cancel the invertible tensor map.
The proof applies to equal indices, zero inputs and nonflat coefficient maps.
The item's DAG proof and dependencies have been updated to this argument.
All additional imports are private proof imports.

The singleton-evaluation-mate, singleton-derived-extension and evaluation-topos
nodes are used as tools from other units, as is the existing system tensor
reduction theorem. These tools establish evaluation adjoints and compatibility
of the existing maps; the unit's prescribed finite-map construction is retained.
No maintainer `tool_uses` approval is added by this delivery.

## Proved and sorry left

Closed one hole: `WeilConjectures.SemilinearSections.scalarTensor_composition`
(node `lem-sp-semilinear-scalar-tensor-composition`).
Added zero holes. No `sorry` remains in the delivered module. Both private helpers
are fully proved. No other module is changed.

## No longer needed

None: no existing import, declared dependency, node or module is pruned.
The original definition dependencies remain needed. The new proof reuses the
existing tensor/reduction calculation instead of repeating a chain-map
coherence calculation on K-flat representatives in this module.

## Where the brief, the DAG or earlier work was wrong

The DAG's proposed direct representative comparison was unnecessary: the
already proved tensor/reduction formula and singleton evaluation mate give a
shorter cancellation argument. No mathematical statement or definition was
changed. In particular, the proof never assumes that derived evaluation detects
equality of morphisms, nor that arbitrary scalar restrictions are flat.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
