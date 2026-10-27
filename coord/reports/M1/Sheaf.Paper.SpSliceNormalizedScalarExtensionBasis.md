## What changed

Filled `AlgebraicGeometry.ProEtale.spSliceNormalizedScalarExtensionBasis` with the
section-reconstruction and sheafification argument specified by its node. The proof
reuses the proved `localTensorBasisIso` helper from
`Sheaf.Paper.SpSliceScalarExtensionBasis`, keeps the ordinary mate unit equation,
and checks the final normalization on every slice section. All new helpers are
private and proved. The theorem signature and public imports are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.spSliceNormalizedScalarExtensionBasis`
(`lem-sp-slice-normalized-scalar-extension-basis`). No holes added or split off.
No `sorry` remains in the item module. A server single-file check passed in
46.3 seconds. An initial delivery probe exceeded 60 seconds, so profiling was used
to improve the private definitions: the scalar-extension mate is now irreducible
after proving its unit API, and the slice-linearity calculation has explicit
intermediate types. No shared definition or importer interface was changed.
Profiler options were removed before the final delivery check.

## No longer needed

No modules or nodes are withdrawn. No existing import was removed. The direct
proof dependency `def-pur-sheaf-tensor-product` is replaced by the existing
`lem-sp-slice-scalar-extension-basis` construction; it remains a statement
dependency. The proof uses the ordinary part of the section-scalar comparison
and selects no derived comparison or resolution data. The tensor-basis
construction is reused from the existing slice-basis module.

## Where the brief, the DAG or earlier work was wrong

The supplied plan applies. The earlier unnormalized slice-basis theorem already
contains a complete tensor-basis construction, but its existential conclusion
forgets the unit formula. Reusing that construction while retaining the mate and
sheafification unit equations closes the normalization obligation without
another split. Zero coefficient rings and empty slices require no extra case.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
