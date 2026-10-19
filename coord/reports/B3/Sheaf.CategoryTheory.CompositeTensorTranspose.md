## What changed

Proved both theorems in `Sheaf.CategoryTheory.CompositeTensorTranspose` directly from
Mathlib adjunction naturality and the existing `Functor.ProjectionFormula` equations.
Two proved private helpers express the tensor-counit associativity calculation and the
inverse transpose of `tensorCounitTranspose`. All existing statements, definitions,
visibility, and imports are unchanged. The proof follows the node's four-step plan.

For the restricted theorem, the tensorator and associator are kept together as one
morphism between the recorded full-domain objects. No tensor closure or additional
membership hypotheses are used. The naturality equation at `q` gives its counit
identity, and projection associativity gives the explicit common inverse transpose.

Validation: the complete module compiles without errors or warnings through
`lcompile.py` (3.4 seconds). The delivery preflight additionally checks every
constant's axioms.

## Proved and sorry left

Closed 2 of 2 original holes:
- `SecSmoothPurity.composite_tensor_transpose`.
- `SecSmoothPurity.CompositeTensorLocalData.composite_tensor_transpose_restricted`.

Both belong to `lem-pur-composite-tensor-transpose`. Holes added: 0. Holes left: 0.
No statements were split off.

## No longer needed

None. All three public imports support the existing signatures and definitions.
Both declared dependencies remain needed: `def-sfb-projection-formula` supplies the
projection structure and its coherence equations, and
`def-weil-pbc-composite-adjunction` supplies Mathlib's composite adjunction and counit.
The unit-coherence equation is not needed in either computation; associativity,
projection naturality, and monoidal unitor naturality suffice. No dependency node or
module is pruned.

## Where the brief, the DAG or earlier work was wrong

No correction needed. The existing proof plan is realized without changing the route.
The global docstring's reference to projection unit coherence is stronger than needed:
the explicit calculation uses no projection unit equation. The restricted-domain
statement correctly records all memberships needed for the proof.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
