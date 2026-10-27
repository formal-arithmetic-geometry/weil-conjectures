## What changed

Filled the explicit integral adjunction transport, its completed scalar comparison,
its comparison to any specified exceptional adjunction, and the realized composition
and Cartesian base-change equations in `Sheaf.Paper.TransportIntegralCounitRealization`.
All existing declaration signatures and public imports are preserved. Private proved
helpers assemble the natural realized gamma and transport scalar comparison records.
The DAG records the two existing factor theorems used by the geometric clauses.
The original redundant instance binders are retained with a narrowly scoped unused
section-variable linter setting; no downstream interface is changed.

## Proved and sorry left

Closed five of the eight original holes, with no new holes:

- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.integral_stage`.
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.coefficient_stage`.
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.fixed_coefficient_stage`.
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.Coherence.composition_realization`.
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.Coherence.baseChange_realization`.

The three remaining original holes are unchanged, all attached to
`lem-pur-transport-integral-counit-realization`:

- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.condensed_stage`.
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.chart_realization`.
- `AlgebraicGeometry.ProEtale.TransportIntegralCounit.integral_counit_realization`.

The closed geometric clauses use the existing stated tower factor theorems, whose
proofs remain separate work. The other three closures use recorded realization
properties, elementary natural-transformation algebra, and Mathlib adjunction
transport and right-adjoint uniqueness.

## No longer needed

No imports removed or modules withdrawn. The dependency
`det-sp-unique-adjoint-coefficients` is pruned from this node: direct conjugation
by Mathlib rightAdjointUniq comparisons proves the fixed scalar clause, including
its unit, counit and actual purity square. No separate coefficient uniqueness
theorem is used. The three remaining original holes still require the original
condensed, chart, finite-reduction and trace normalization dependencies. The composition and base-change factor modules were already public imports needed by the existing statement words; their theorem
nodes are now explicitly included in proof_deps.

## Where the brief, the DAG or earlier work was wrong

The existing proof_deps omitted `det-sp-composition-factors` and
`det-sp-purity-bc-factors`, although the module includes separate geometric
realization clauses whose docstrings call for precisely those identities.
These dependencies and their elementary realization steps are now recorded.
The coefficient-uniqueness dependency also had an obsolete Lean attachment; its
result is unnecessary for the direct conjugation proof. No mathematical statement
or definition was changed. The unit route is preserved.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
