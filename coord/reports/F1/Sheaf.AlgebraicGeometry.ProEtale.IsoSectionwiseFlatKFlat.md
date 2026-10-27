## What changed

Closed the parent conjunction theorem by applying two strictly smaller preservation theorems. Added `IsoSectionwiseFlat` for flat module sheaves and `IsoSectionwiseKFlat` for independent-coefficient K-flat complexes; both are proof obligations split from the tensor argument and are imported privately by the parent.

## Proved and sorry left

The parent declaration `AlgebraicGeometry.Scheme.isoSectionwiseModuleInverseImage_flat_kFlat` is closed by a real conjunction proof. Two strictly simpler child declarations remain as named proof obligations:

- `AlgebraicGeometry.Scheme.isoSectionwiseModuleInverseImage_preservesFlat` (node `lem-pod-sectionwise-flat-kflat-flat`), `:= by sorry`.
- `AlgebraicGeometry.Scheme.isoSectionwiseModuleInverseImage_preservesKFlat` (node `lem-pod-sectionwise-flat-kflat-kflat`), `:= by sorry`.

Actual counts: one existing sorry closed; two split-off sorries added. No definitions contain `sorry`.

## No longer needed

The parent proof no longer directly uses its former tensor and K-flat proof dependencies; it uses the two child nodes, which retain those dependencies in their own statements and proof plans. No existing dependency module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original DAG bundled flat-module and K-flat preservation into one theorem without separate declarations for the two substantial tensor arguments. The parent is now reduced to their conjunction, while each child states one strict clause of the original result. No statement or definition was changed.

## New nodes

`lem-pod-sectionwise-flat-kflat-flat` records the flat-module preservation clause and is realized by `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseFlat`.

`lem-pod-sectionwise-flat-kflat-kflat` records the independent-coefficient K-flat preservation clause and is realized by `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseKFlat`.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
