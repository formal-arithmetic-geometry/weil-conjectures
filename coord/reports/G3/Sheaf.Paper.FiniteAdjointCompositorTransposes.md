## What changed

Replaced the sole sorry in `Sheaf.Paper.FiniteAdjointCompositorTransposes`.
Two proved private categorical helpers implement counit-compatible uniqueness
and the coefficient square for transported adjunctions. The main proof constructs
both exceptional compositors, proves their uniqueness, computes the iterated
coefficient transpose using the f and g counit equations and naturality of
`bg.inv`, and applies injectivity of the composite Hom equivalence to the
coefficient square. The pasted coefficient isomorphism includes the functor
associators explicitly.

All public statements, definitions, and imports are unchanged. The proof follows
the existing five-step DAG plan and the current blueprint comparisons proof
(1)-(2). The mathematical argument is valid for arbitrary categories and scalar
functors; it uses no flatness or finite projective-dimension assumption.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.finiteAdjointCompositorTransposes`
(node `lem-sp-finite-adjoint-compositor-transposes`): 1 of 1 original holes.
Added: none. Remaining in the delivered module: none. No split-off statements.

The two private helpers `normalized_compositor` and
`normalized_coefficient_square` have complete proofs.

## No longer needed

None. The proof uses both recorded Mathlib leaves:
`def-weil-pbc-composite-adjunction` and `det-sp-unique-right-adjoint`.
No imports are removed. The public imports still supply the existing definitions
and statement interfaces. No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The specialized geometric normalization and
coefficient-map identifications are already included in the supplied data; the
formal conclusion needs only their adjunction and counit equations. Identity
functors, zero objects and non-flat coefficient changes require no special cases.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
