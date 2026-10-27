# AlgebraicGeometry.strictEtaleScalarTransportProjection interface

## Reason

The scalar adjoint proof needs a named intermediate for the finite-free scalar
extension construction. Its public statement mentions `StrictEtaleTransportProjection`,
so the module must publicly expose the existing projection interface.

## Old

`Sheaf.Paper.EtaleCoefficientSystemAdjoint` imported
`Sheaf.Paper.StrictEtaleIsomorphicStageProjection` privately and had the scalar theorem's
finite-free construction left as one `sorry`.

## New

The import of `Sheaf.Paper.StrictEtaleIsomorphicStageProjection` is public. The module
adds the public theorem `AlgebraicGeometry.strictEtaleScalarTransportProjection`, which
states the target compact-support system, exceptional adjoint, coefficient transports,
transport projection, and finite-level mate isomorphisms. The original scalar theorem
assembles this intermediate with the existing proved `exceptionalTransportOfProjection`.
No existing declaration signature is changed.

## Users

The module's existing importers see the same declarations plus the projection interface;
no consumer requires adaptation. The unfinished parent node continues to depend on the
original scalar theorem.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleCoefficientSystemAdjoint | H2 | New intermediate theorem and public projection import. |
| Existing importers of Sheaf.Paper.EtaleCoefficientSystemAdjoint | unclaimed or current holders | Compile unchanged; no signature changes. |

## Status

landed 20261026T023250-L-538296 2026-10-26 (merge of deliver/H2/Sheaf.Paper.EtaleCoefficientSystemAdjoint)
