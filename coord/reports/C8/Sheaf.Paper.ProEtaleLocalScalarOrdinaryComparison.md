## What changed

Filled `AlgebraicGeometry.Scheme.LocalScalar.ordinaryComparison` in the item module.
All added helpers are private and proved. Public signatures, definitions, instances,
and public imports are unchanged.

The geometric comparison follows from uniqueness of left adjoints. The proof checks
the constant-section normalization and the coefficient square on the right adjoints,
then composes the module inverse-image, ordinary tensor, and fixed-scalar adjunctions.
The slice comparison uses the already proved module sheafification comparison from
`LocalizedSiteTensorRestriction` and the recorded ordinary object/map equations.
The node now records this route. Four proof imports provide the reused constructions.
Local irreducibility keeps the final composition from unfolding the large extension
constructions; the final proof is a direct term. The complete module compiles through
`lcompile.py` in 51.7 seconds with no warnings or errors.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.LocalScalar.ordinaryComparison`
(node `lem-sfb-proetale-local-scalar-ordinary-comparison`).

No sorry remains in the item module. No holes were added or split off.
This is a proof from existing declarations, including the existing scalar-extension
universal-property witnesses; it is not a decomposition.

## No longer needed

- `lem-per-independent-scalar-inverse-image` and
  `Sheaf.CategoryTheory.ScalarInverseImageIndependent`: the adjunction proof works
  directly on the actual pro-etale sites and avoids algebraic-inverse-image transport.
- `lem-weil-pbc-site-constant-restriction`: the target ring on the slice remains the
  restricted global constant ring, so no identification with a newly formed constant
  ring on the slice is needed.

These planned dependencies were not imported. The localized tensor restriction module
is still needed for its proved module sheafification comparison. No existing module
is withdrawn. No existing import was removed.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and valid also for B=0 and empty slices. The original plan
was mathematically sound but its inverse-image transport can be replaced by the
shorter comparison of the explicit right adjoints. The unit route is unchanged.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
