## What changed

Proved `AlgebraicGeometry.ProEtale.integralResidueClass_triangle_closure` in
`Sheaf.Paper.IntegralResidueClassTriangleClosure` without changing any public signature,
definition or public import. Added three proved private helpers: quotient residue
discreteness and equality of the underived and derived forward normalized encodings.
The latter uses the normalization equations and sheafification extensionality, so the
existential encoding predicate becomes the inverse image under one exact functor.
Completeness comes from `CompleteIntegralResidue.complete_integral_residue_functor`;
residue-origin closure comes from
`isBoundedConstructibleFiniteCoefficient_isTriangulated`.

The actual derived reduction is triangulated by its adjunction with exact restriction,
using Mathlib's compatible adjoint shift structure. Intersections and inverse images
of triangulated object properties then give every requested clause. Updated the item's
DAG proof and proof dependencies to describe this argument. The existing seven-step
Lean docstring describes the older expanded argument; the new DAG records the exact
compiled assembly. The declaration-local unused-variable linter option preserves the
original named but necessarily unused isomorphism binder in the theorem statement.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.integralResidueClass_triangle_closure`
(node `lem-sfb-integral-residue-class-triangle-closure`).
Added 0 holes; split off 0 statements; 0 `sorry` remain in the delivered module.
The existing completeness theorem remains an imported proof dependency, as intended
by stage 3; no claim is made that its transitive axioms are already sorry-free.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Paper.ProEtaleConstantModuleEncoding`;
- `Sheaf.Paper.CompletionTriangleComparison`;
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`;
- `WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf`;
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect`.

Replaced them by `Sheaf.Paper.CompleteIntegralResidueFunctor`,
`Sheaf.AlgebraicGeometry.PullbackBoundedConstructible` and
`Mathlib.CategoryTheory.Triangulated.Adjunction`. Public imports are preserved for
existing consumers. No module is withdrawn: the removed imports may remain needed
transitively or by other consumers.

The parent's old direct tool uses are no longer direct steps:
`lem-pe-completion-triangle-comparison`, `lem-pur-derived-change-of-rings`,
`lem-weil-pbc-proetale-constant-module-encoding`,
`lem-weil-pbc-fixed-module-constructible-origin`,
`lem-weil-pbc-fixed-module-bounded-constructible-origin`,
`lem-weil-proetale-dbc-triangulated`, and
`lem-sf-module-object-ordinary-coefficient-equivalence`.
Their old tool-use approvals are removed from this node; this does not remove their
uses inside the retained completeness and finite-origin closure dependencies.
Both current declared closure dependencies are retained. The continuous-ring
relabeling clauses of the completeness theorem are not needed because the unchanged
predicate already uses the fixed encoding and recorded finite realization.

## Where the brief, the DAG or earlier work was wrong

The module's seven-step proof docstring predates the current DAG's two-result split.
The current DAG's assertion that its normalized residue functor is precisely the
functor in this predicate was not an immediate definitional equality of the Lean
interfaces. Rather than assume that identification, the proof fixes one normalized
encoding, proves independence from that choice, and obtains exactness of the actual
derived reduction directly from its published adjunction. This is a shorter valid
route below the same unit, using the same completeness and finite-origin results.
Single-file validation through `lcompile.py` passes with no warnings. All new private
helpers are proved, and all lines are within 100 columns. No statement dispute,
source-library edit, consumer adaptation or new node is needed.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
