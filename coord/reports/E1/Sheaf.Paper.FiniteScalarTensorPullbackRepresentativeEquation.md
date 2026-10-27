## What changed

The target module keeps its original representative-equation statement and records the
remaining proof hole.  Two strictly simpler intermediate statements were added: the
coefficient realization equals its representative-descent construction, and the finite
scalar total tensor component has the required ordinary normalization.  Both intermediate
modules compile and are ready for follow-up proof work.

## Proved and sorry left

No original hole was closed.  The target theorem
`finiteScalarTensorRealization_Y_representative` remains a named `sorry`.  The two new
intermediate theorems also remain named `sorry`:

- `finiteScalarTensorRealizationForCoefficients_eq_representatives`;
- `finiteScalarTotalTensorIso_representative_component_eq`.

## No longer needed

None.  The attempted direct proof route used only the existing representative
factorization declaration together with the two split intermediate statements; no
additional imports or DAG nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The declared representative-factorization route is mathematically appropriate, but
opaque nested realization and total-tensor definitions make the final specialized
composition exceed the single-file kernel-check time when combined in this module.
The route was therefore split at the two concrete component equalities above, each of
which compiles independently.

## New nodes

- `lem-sf-finite-scalar-tensor-realization-coefficients-equality`
- `lem-sf-finite-scalar-total-tensor-iso-representative-component-equality`

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
