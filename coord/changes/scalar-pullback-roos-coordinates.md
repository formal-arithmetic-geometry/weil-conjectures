# Scalar pullback Roos coordinate predicate relocation

## Reason

The tensor-unit predicate is placed in its own public module. Its signature is
unchanged; this is a declaration relocation. The attempted split of the proof
obligation was withdrawn after review because its arbitrary-isomorphism generator
statement was false.

## Old version

`ScalarPullbackQuotientFormula` was declared in
`Sheaf.Paper.ScalarPullbackRoosCoordinates`.

## New version

`ScalarPullbackQuotientFormula` is declared in
`Sheaf.Paper.ScalarPullbackQuotientFormula` and publicly imported by the item.
The item retains the original single theorem obligation and publicly imports the
predicate module.

## Users

- `Sheaf.Paper.ScalarPullbackLeftRoos`: imports the item and uses the predicate.
- `Sheaf.Paper.ScalarPullbackRightRoos`: imports the item and uses the predicate.
- `Sheaf.Paper.ScalarTowerPullbackLimitBridge`: imports the item and uses the
  coordinate existence theorem.

All users retain the same declaration names and signatures.

## Status

The two invalid split-off modules are withdrawn; the predicate relocation remains.
