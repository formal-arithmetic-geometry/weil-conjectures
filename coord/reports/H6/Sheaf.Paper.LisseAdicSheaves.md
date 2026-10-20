## What changed

Proved both existence theorems in `Sheaf.Paper.LisseAdicSheaves`.
Integral scalar extension is constructed from sheafified balanced scalar extension,
with quotient-induced transition maps. Local trivializations prove finite local
constancy. The stalk scalar-extension comparison and tensor right exactness prove
the transition surjectivity and kernel condition.

Constructed the identity and composition comparisons of integral scalar extension.
Their tensor-generator formulas prove the associativity and unit identities.
Rationalizing these comparisons gives the coherent pseudofunctor over finite
coefficient fields, with precisely the prescribed objects and scalar-extension maps.

Added proof imports for sequence functors, scalar adjunctions, DVR ideal powers,
quotient restriction, the stalk tensor comparison, and locally discrete
pseudofunctors. Updated the definition node's proof and proof dependencies to match.
Proof-only comparison APIs remain irreducible after their construction sections,
preventing repeated expansion of their data. Generic tensor lemmas use the same
field instances as the coefficient constructions, and the rational-map proof avoids
large local object aliases. All added helpers are private and proved. Existing public statements,
definitions, attributes and public imports are preserved. The complete file compiled without
warnings in 47.6 seconds through `lcompile.py`.

`coord/changes/H6-lisse-adic-proof-support.md` records the private quotient-helper
Ring generalization, replacement of the private balanced-map implementation, and
proof-local commands required by preflight. Its user check found no external uses
of the changed or removed private declarations; no consumer adaptation is needed.

## Proved and sorry left

Closed both original holes (2 of 2):

- `AlgebraicGeometry.Scheme.lisseIntegralScalarExtension_exists`.
- `AlgebraicGeometry.Scheme.lisseCoefficientDiagram_exists`.

Both belong to `def-pod-lisse-l-adic-sheaves`. No `sorry` remains in the module.
No holes were added elsewhere; none were split off. This is a proof, not a
decomposition.

## No longer needed

No modules, DAG nodes, or public imports are withdrawn. The old private
`scalarBilinear`, `scalarBilinear_apply`, and `scalarBilinear_balanced` construction
is replaced by Mathlib's semilinear `TensorProduct.map`. The finite-level
extensionality and scalar-linearity arguments reuse the generic quotient-sheaf
lemmas instead of repeating their proofs with concrete coefficient rings.

## Where the brief, the DAG or earlier work was wrong

No public statement or definition correction was needed. The definition node originally
had no numbered proof plan. Its updated proof records the explicit construction,
stalk calculation, and coherence argument. The unit route and the node's existing
Lean attachment are preserved.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
