## What changed

Added the real assembly proof of `native_row_hom_comparison`. The substantial representative
transport is split into `native_row_hom_data` and the normalization equality into
`native_row_hom_eta_eq`; the item theorem combines them and supplies the final `HEq` by transitivity.

## Proved and sorry left

`native_row_hom_comparison` is proved. Two strictly smaller transport lemmas remain as `sorry`:
`native_row_hom_data` (node `lem-sf-weil-native-row-hom-data`) and `native_row_hom_eta_eq`
(node `lem-sf-weil-native-row-hom-eta-eq`).

## No longer needed

No imports were removed. The proof uses the existing native closed model and ringed two-injective
model declarations.

## Where the brief, the DAG or earlier work was wrong

The planned sign-construction details are substantial and are not available as executable APIs in
the current declarations; they were correctly isolated as two strict intermediate statements.

## New nodes

`lem-sf-weil-native-row-hom-data` and `lem-sf-weil-native-row-hom-eta-eq` are added in the item
node chapter. No change records are needed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
