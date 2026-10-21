## What changed

Restored the quarantined `Sheaf.Paper.CondensedPointSupertrace` module and reduced its
main existence theorem to a real constructor from seven separately named component
results. The component results are public theorem statements with the source proof
obligations recorded in their docstrings; the final theorem combines their witnesses
into `CondensedPointSupertraceData`. The module compiles against the current library.

## Proved and sorry left

The main theorem `AlgebraicGeometry.ProEtale.condensed_point_supertrace` is proved by
constructing the structure from the component witnesses. Seven strictly smaller
component theorems remain as `sorry`: `condensed_point_realization_exists`,
`condensed_point_scalar_exists`, `condensed_point_matrix_exists`,
`condensed_point_tensor_model_exists`, `condensed_point_tensor_compatibility`,
`condensed_point_cohomology_exists`, and `condensed_point_duality_exists`.

## No longer needed

No imports were removed. The proof uses the existing declarations and the component
interfaces declared in this module; no additional DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The archived module had one monolithic theorem hole despite a proof plan with seven
independent construction obligations. Splitting those obligations gives a compiling
constructor proof while preserving the target statement and all existing definitions.
The archive was also absent from the live tree after the cluster restore; this delivery
restores it in the sandbox.

## New nodes

Seven new DAG nodes were added for the split component theorems; each is recorded in
`dag/nodes/sec-zeta-weil/` and points to the corresponding declaration in the module:

- `lem-zl-condensed-point-supertrace-realization`
- `lem-zl-condensed-point-supertrace-scalars`
- `lem-zl-condensed-point-supertrace-matrices`
- `lem-zl-condensed-point-supertrace-tensor-model`
- `lem-zl-condensed-point-supertrace-tensor-laws`
- `lem-zl-condensed-point-supertrace-cohomology`
- `lem-zl-condensed-point-supertrace-duality`

The interface change is recorded in `coord/changes/condensed-point-supertrace-components.md`.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
