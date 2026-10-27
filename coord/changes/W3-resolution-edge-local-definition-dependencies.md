# Fixed local-comparison definition dependencies

## Reason

Three existing, proved unit-normalization nodes still name
`lem-weil-pbc-derived-adjunction-top-edge` as a statement dependency for the definitions
of the local-class and comparison maps. Those definitions were moved verbatim to
`DerivedAdjunctionTopEdgeData`, attached to `def-weil-pbc-truncated-counit-edge`.
Using these proved nodes below the resolution-edge obligation would otherwise close
a spurious DAG cycle through the higher edge theorem. Their actual Lean imports
already use the data module and are cycle-free.

## Old

For each of `lem-weil-pbc-direct-image-complex-unit`,
`lem-weil-pbc-local-hypercohomology-complex-unit-class`, and
`lem-weil-pbc-direct-image-resolution-normalization`, the old `stmt_deps` is verbatim:

```json
[
  "lem-weil-pbc-derived-adjunction-top-edge",
  "lem-trf-unbounded-direct-image-section-presheaf"
]
```

## New

For each of those three nodes, the new `stmt_deps` is:

```json
[
  "def-weil-pbc-truncated-counit-edge",
  "lem-trf-unbounded-direct-image-section-presheaf"
]
```

Only the dependency metadata changes. Each node's statement, Lean attachment, proof,
and proof dependencies remain verbatim. No Lean signature, attribute, import,
instance, or definition changes. No target's meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DirectImageComplexUnit | unclaimed in shared records; proved B3 delivery | Node statement dependency points to its actual definition module; Lean unchanged. |
| Sheaf.AlgebraicGeometry.LocalHypercohomologyClassUnit | unclaimed in shared records; proved B3 delivery | Same metadata-only correction; Lean unchanged. |
| Sheaf.AlgebraicGeometry.DirectImageResolutionNormalization | unclaimed in shared records; proved B3 delivery | Same metadata-only correction; Lean unchanged. |
| Sheaf.AlgebraicGeometry.DerivedResolutionEdgeLocal | W3 | Can cite these existing proved steps without introducing a false DAG cycle. |

Every mathematical and Lean consumer is unaffected because no declaration or
mathematical statement changes. Direct-importer recompilation for an interface
change is unnecessary: there is no Lean interface change in these modules.

## Status

landed 20261026T135924-L-4073374 2026-10-26 (merge of deliver/W3/Sheaf.AlgebraicGeometry.DerivedResolutionEdgeLocal)
