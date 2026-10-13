# RingTensorCohomology.spanLeft_isIso proof import

## Reason

Reuse the existing proved scalar-extension quasi-isomorphism helper instead of
adding a duplicate theorem, as required by the returned landing refusal.
Its private visibility is supported by a proof-only `import all`; no library
interface or definition changes, and no other module is adapted.

## Old

The base module has no proof import of
`Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso` and
`spanLeft_isIso` is `by sorry`.

## New

The module has `import all Sheaf.Algebra.Homology.KFlatScalarExtensionDerivedIso`.
`spanLeft_isIso` applies `CochainComplex.scalarExtension_quasiIso_of_kFlat`
after proving the resolved restricted augmentation is a quasi-isomorphism
between K-flat complexes. No new helper is declared.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RingTensorCohomology | A3 | proof-only import and proof |

## Status

landed 20261013T082328-L-1629850 2026-10-13 (merge of deliver/A3/Sheaf.Algebra.Homology.RingTensorCohomology)
