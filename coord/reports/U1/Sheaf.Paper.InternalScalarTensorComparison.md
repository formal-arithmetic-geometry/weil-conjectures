## What changed

Proved both holes of `Sheaf.Paper.InternalScalarTensorComparison`, preserving every
existing public signature, definition body, instance attribute, public import and docstring.
The assigned module now privately imports two proved generic helper modules:

- `Sheaf.CategoryTheory.ModuleObjects.ScalarTensorCancellation` constructs tensor
  cancellation from the bimodule associator and right unitor, proves naturality, and
  transfers exactness through the forgetful functor to prove preservation of flat objects.
- `Sheaf.CategoryTheory.ModuleObjects.ScalarExtensionMonoidal` constructs lax monoidal
  restriction by balanced descent and equips its left adjoint with the canonical oplax
  structure. Concrete bimodule isomorphisms identify its unit and tensor maps as
  isomorphisms and prove the scalar-unit normalization.

The assigned module proves uniqueness by injectivity of the scalar extension adjunction
and cancellation of the balanced tensor projection. Equality of the tensor maps forces
unit equality by monoidal unitality. The derived definitions use their original bodies.
Both generic constructions cover identity scalar maps and the zero algebra: neither
argument uses nontriviality, faithful flatness, or flatness of the coefficient algebra.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.internalScalarMonoidalNormalized_existsUnique`.
- `AlgebraicGeometry.ProEtale.CondensedRing.internalScalar_preservesFlat`.

The new public theorems `CategoryTheory.Mod.exists_extendScalarsMonoidal` and
`CategoryTheory.Mod.extendScalars_preservesFlat` are proved completely. Every private
helper is proved or is an explicit data construction with all fields supplied.
Zero holes remain in the assigned module or the new modules; zero holes were added,
and zero statements were split off with unfinished proofs. This is a proof of both
original holes, not a decomposition into new holes.

## No longer needed

No original imports, modules, nodes, or declarations were removed. The original node
had no proof dependencies to prune. The proof uses the generic internal-module API
and Mathlib's bimodule associator/unitors, without the separate ring-sheaf scalar
comparison models. No source-library declaration was changed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The original node had an empty proof plan, whereas
its Lean docstrings supplied the intended balanced tensor and flatness arguments.
The completed proof records that argument explicitly in the DAG. The existing
`Mod.monoidal_extendScalars` requires an invertible coefficient map, so it cannot
supply the arbitrary scalar-extension structure needed here.

## New nodes

`lem-sfb-internal-extension-preserves-flat` records the proved general preservation
of categorically flat internal modules by scalar extension. Its Lean module is
`Sheaf.CategoryTheory.ModuleObjects.ScalarTensorCancellation`; its source is the
Stacks change-of-rings flatness proof via balanced tensor cancellation.

`lem-sfb-internal-extension-monoidal` records the proved existence of a normalized
strong monoidal structure for generic internal scalar extension. Its Lean module is
`Sheaf.CategoryTheory.ModuleObjects.ScalarExtensionMonoidal`; the assigned module
adds the uniqueness argument. Both nodes inherit the assigned node's chapter and unit.
No change record is needed: no existing interface or definition was altered.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
