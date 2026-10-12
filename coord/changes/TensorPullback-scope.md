# Sheaf.AlgebraicGeometry.TensorPullback scope command

## Reason
The proof uses Mathlib's `ChangeOfRings` tensor notation. The file-level scoped command is proof support only and does not add declarations or alter definitions.

## Old
No `open scoped ChangeOfRings` command.

## New
`open scoped ChangeOfRings`.

## Users

| module | group holding it | effect |
|---|---|---|
No downstream module is affected. `open scoped ChangeOfRings` activates notation only while elaborating this file; importing modules do not inherit the open scope.

## Status
landed 20261012T023506-L-1118981 2026-10-12 (merge of deliver/S1/Sheaf.AlgebraicGeometry.TensorPullback)
