## What changed

Filled eight of the twelve theorem proofs in
`Sheaf.Paper.FiniteProductFieldCoefficientDescent`: the Hom tensor formula,
common-field object lifting, common-field arrow lifting, eventual component
 equality, rational tensor existence and uniqueness, rational unit existence and
uniqueness, rational scalar-unit existence and uniqueness, and common unit
existence and uniqueness. The proofs use the recorded localization, tensor,
pullback, and stage-system APIs; public definitions and theorem signatures are
unchanged. The item module compiles within the file limit.

## Proved and sorry left

Proved declarations:
`hom_tensor_formula`, `objects_at_common_field`, `arrows_at_common_field`,
`component_equality_iff_eventual`, `rational_tensor_existsUnique`,
`rational_unit_existsUnique`, `rational_scalar_unit_existsUnique`, and
`common_unit_existsUnique`.

Four original sorries remain, all under
`lem-pur-finite-product-field-coefficient-descent`:
`restriction_equivalences`, `rational_tensor_scalar_compatible`,
`rational_unit_scalar_compatible`, and `common_tensor_existsUnique`.
No new sorries were added.

## No longer needed

No imports or DAG modules were withdrawn. The proof uses the existing public
imports and private helper arguments in the item module; exploratory modules
are not part of the delivery.

## Where the brief, the DAG or earlier work was wrong

The stated common tensor dependency requires its own canonical compatible unit
family, while the item hypothesis supplies scalar-unit comparisons separately.
The tensor-square calculation can be proved from the localized integral tensor
square, but the common-stage assembly still needs the declared common tensor
descent result.

## New nodes

None.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
