## What changed

Filled all three theorem proofs in `Sheaf.Paper.ParameterRootBoundaryData` without changing
any statement, definition, public name or import. The proof follows the existing declaration
docstrings and node's elementary well-definedness argument: evaluate the two families of
relations, identify the composite ring map on constants, and use the second projection of the
pullback lift for the profinite test square.

The library and Mathlib searches found the required elementary APIs (`Ideal.span_le`,
`Ideal.Quotient.lift_mk`, `MvPolynomial.eval₂Hom_C`, `MvPolynomial.eval₂Hom_X'`,
`Spec.map_comp`, and `pullback.lift_snd`). No additional theorem dependencies are introduced.

## Proved and sorry left

Closed three existing holes, all attached to `def-sfb-parameter-root-boundary-data`:

- `AlgebraicGeometry.ProEtale.RootBoundary.roots_vanish`.
- `AlgebraicGeometry.ProEtale.RootBoundary.boundary_square`.
- `AlgebraicGeometry.ProEtale.RootBoundary.test_boundary_square`.

Zero holes added, zero split off, and zero holes remain in the item module.
Remote single-file compilation succeeded in 4.3 seconds with no warnings.
`#print axioms` for each of these three declarations reported exactly
`propext`, `Classical.choice`, and `Quot.sound` (no `sorryAx`).
Temporary axiom-print commands were removed before delivery.
The argument uses only positivity of root orders, so it retains arbitrary p, including 0
and 1; empty parameter tuples, the zero ring and empty profinite tests are included without
additional assumptions. For a divisibility relation, positive m and n with n dividing m
ensure m/n is positive, including the case m=n.

## No longer needed

None. The existing three public imports supply the root presentation, affine projection,
and actual profinite test construction. No nodes or modules are pruned and no unit route
is bypassed. No new proof imports are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The definition node has an empty formal proof list;
its statement's well-definedness explanation and the three Lean declaration docstrings
already give exactly the elementary argument implemented here. No route change is needed.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
