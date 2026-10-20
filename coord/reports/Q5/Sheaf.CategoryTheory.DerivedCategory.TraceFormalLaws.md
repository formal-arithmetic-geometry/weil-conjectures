## What changed

Restored the quarantined module with all six theorem bodies proved in
`Sheaf.CategoryTheory.DerivedCategory.TraceFormalLaws`, preserving all public
statements, definitions and public imports. All new helpers are private and proved.
The delivery also updates the proof route of `prop-trf-trace-formal-laws`.

The returned packet predates quarantine. This repair restores the complete module
at its original Lean path and retains its existing node attachment. It also fixes
the quarantine compiler error: `traceExtendScalarsAdditive` now uses
`(ModuleCat.extendRestrictScalarsAdj ρ).left_adjoint_additive` in place of the
removed `ModuleCat.extendScalars_additive_sheaf`. The instance type is unchanged.
The change record is `coord/changes/trace-extend-scalars-additive.md`.

Validation: the restored complete module compiled without errors or warnings
through `lcompile.py` in 6.0 seconds against the current server library. All six public theorem signatures were compared
with the shared source and remain unchanged. The added cohomology-splitting import
passes the import-direction cycle check. There are no `sorry` tokens in the module.

The coefficient ring is a quotient of the local DVR of integers. Finite projective
modules over it are free; the proof handles the zero ring separately. This lets
filtered additivity and arbitrary derived scalar extension reuse the adopted
source library's proved finite-free trace calculations. The filtered replacement
and K-flat counit remain genuine dependencies. The scalar-extension proof uses
counit naturality and proves perfection of the extended model without a flatness
assumption on the target.

The counterexample constructs the two-term Z/4 complex, its endomorphism, its short
exact sequence and the explicit null-homotopy, then uses Mathlib's distinguished
short-exact-sequence triangle and calculates its nonzero trace. The field law
uses the existing field-cohomology splitting theorem only to obtain perfectness,
and the already proved Hopf trace formula supplies the trace identity.
Common-stage independence uses the faithful realization, scalar-extension trace
compatibility and conjugacy. Cocone Hom surjectivity supplies a finite-stage
presentation for uniqueness; no equivalence with the whole derived category of
the algebraic closure is claimed.

## Proved and sorry left

Six holes closed relative to the quarantined source, by declaration:

- `DerivedCategory.perfectCategoricalTrace_conjugacy`.

- `DerivedCategory.perfectCategoricalTrace_filtered_additivity`.
- `DerivedCategory.perfectCategoricalTrace_triangle_counterexample`.
- `DerivedCategory.perfectCategoricalTrace_scalar_extension`.
- `DerivedCategory.perfectCategoricalTrace_cohomology`.
- `DerivedCategory.perfectCategoricalTrace_common_stage`.

Zero holes added or split off. Zero holes remain in the delivered module.
`perfectCategoricalTrace_conjugacy` was proved on the old delivery base, but its
quarantined source contains a hole; its completed proof is restored here. The
old delivery reported five closures against that older base; the restored archive
has six holes and this module has zero. The additivity-instance repair adds no holes.
This is a proof from existing dependencies, including the currently unproved
`DerivedCategory.field_complex_cohomology_splitting`; it does not claim that the
entire transitive import closure has no holes.

## No longer needed

The direct `Sheaf.CategoryTheory.DerivedCategory.ChainSupertrace` proof import and
node `lem-trf-chain-supertrace` are unnecessary for this module: the adopted source
library already proves the finite-free signed chain-trace calculation used here.
Its signed duality construction preserves the route of unit `sk-p-trace`.

Direct proof dependencies `lem-weil-pbc-projective-module-flat`,
`lem-weil-pbc-vector-space-projective` and `def-weil-pbc-projective-module` are
removed: Mathlib supplies flatness of the free coefficient terms and freeness of
vector spaces, and the existing cohomology-splitting node supplies field
perfectness. Their old top-level tool-use approvals are removed in their original
order. These nodes can remain transitively needed by other proofs; no modules or
source-library declarations are withdrawn.

Redundant direct imports also removed (their interfaces remain available through
needed imports): `Mathlib.Algebra.Homology.DerivedCategory.KProjective`,
`Mathlib.RingTheory.Flat.Basic`, `Mathlib.LinearAlgebra.Basis.VectorSpace`,
`Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`,
`Sheaf.Paper.FieldComplexScalarExtension`, and `Sheaf.Paper.PointFdComplexes`.

The planned new canonical-truncation construction and telescoping calculation
are unnecessary because the source Hopf trace theorem already proves the needed
homology trace identity. No truncation support nodes are added.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The DAG did not take advantage of the existing proved
source-library exact-sequence, scalar-extension and Hopf trace formulas. Its
finite-projective plan specializes to finite-free models here because the
coefficient quotient is local. This removes considerable duplicate work while
retaining the signed dual-frame trace and filtered-origin restriction.

The existing node `lem-trf-field-complex-cohomology-splitting` is now a direct
proof dependency. Only its perfectness conclusion is used. It belongs to unit
`sk-thm-trace-transport`, but is generic field-complex infrastructure rather than
a use of that unit's trace-transport conclusion; its own proof does not depend on
this formal-laws node. The maintainer may record the corresponding tool-use
approval; this packet does not add or reorder maintainer approvals.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
