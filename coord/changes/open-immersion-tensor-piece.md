## Reason

The formal proof needs a named projection component and a bundled intermediate result
covering its naturality and invertibility. These are public declarations because the
intermediate theorem is recorded as a DAG node.

## Old

The module had only the target existence statement and its uniqueness theorem; the
existence proof was a single `sorry`.

## New

`openTensorProjectionComponent` is the explicit adjunction transpose. The intermediate
`openTensorProjection_exists` states existence of a natural transformation with these
components and componentwise `IsIso`, and remains the one documented split `sorry`.

## Users

`openImmersionTensor_exists` uses both declarations to construct the natural isomorphism
and prove the normalization equation. No external module is adapted.

## Status

landed 20261021T001132-L-1375871 2026-10-21 (merge of deliver/N4/Sheaf.Paper.OpenImmersionTensorPiece)
