## What changed

Proved `AlgebraicGeometry.Scheme.pbcCompletedSection_naturality` in
`Sheaf.Paper.PbcRationalCategory`. Compose the constant-presheaf sheafification unit
with `pbcCompletedScalar.hom`, apply the composite natural transformation's naturality
at the given restriction map, and evaluate the resulting equality at the scalar.
An explicit `change` keeps the ring-morphism coercions aligned without unfolding
the completed coefficient ring. The module compiles through `lcompile.py`.
All existing signatures, definitions, visibility, imports and docstrings are unchanged.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.pbcCompletedSection_naturality`
(node `def-weil-pbc-rational-category`).
No holes added or split off. Zero `sorry` remain in the delivered module.
The proof uses only naturality and evaluation of an equality; the existing
coefficient constructions retain their existing upstream proof dependencies.

## No longer needed

None. No proof-only imports were present or added. Existing public imports supply
the definitions and instances of the module and remain unchanged. No declared
proof dependencies exist for this definition node; no nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

None. The existing docstring's naturality argument closes the only hole directly.
The node is a definition node with an empty proof plan, so no route change or
node update is needed. The proof does not bypass any blueprint unit or step.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
