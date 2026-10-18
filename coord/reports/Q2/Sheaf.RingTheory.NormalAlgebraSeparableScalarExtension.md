## What changed

Proved `Algebra.isNormal_tensorProduct_of_separableExtension` in
`Sheaf.RingTheory.NormalAlgebraSeparableScalarExtension`, preserving its signature and
public imports. The proof applies the existing separable-field geometric-normality theorem
and the geometrically-normal tensor-normal theorem with `A = K`, then transports normality
from `K ⊗[k] B` to `B ⊗[k] K` using `Algebra.TensorProduct.comm`. For each target prime,
`Localization.localRingEquiv` transports the domain and integrally closed properties.
The file compiles cleanly with `lcompile.py`.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.isNormal_tensorProduct_of_separableExtension`
(node `lem-weil-pbc-normal-algebra-separable-scalar-extension`).
Holes left in the item: zero. Holes added: zero. Split-offs: zero.
The proof uses the existing declarations
`Algebra.normal_tensorProduct_of_isSeparableExtension` and
`Algebra.isNormal_tensorProduct_of_geometricallyNormal`, whose proofs remain sorry in the
library as intended by this stage.

## No longer needed

No imports were removed. The declared proof dependencies are all retained; the tensor swap
and prime-localization transport use Mathlib's `Algebra.TensorProduct.comm` and
`Localization.localRingEquiv` directly. No nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement or definition was found. The written three-step plan is sufficient,
with the final tensor-factor swap implemented by the existing Mathlib algebra equivalence and
its induced local-ring equivalence. Universes are handled by instantiating the geometric
normality hypothesis at `Type (max u v w)`, exactly matching its declaration.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
