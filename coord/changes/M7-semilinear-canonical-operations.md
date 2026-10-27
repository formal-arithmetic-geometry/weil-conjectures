# AlgebraicGeometry.ProEtale.SemilinearProperOpen system operations (withdrawn)

## Reason

The delivery at ea7cfd3b7896 proposed to redefine `coefficients`, `transition`, `Modules`,
`push`, `pull`, `ordinaryAdj`, `P`, `R`, `adj`, `pushComp`, `pullComp`, `pComp`, `sComp`,
`extension`, `ordinaryOpenAdj`, `J` and `levelTower` of
`Sheaf.SixFunctors.SemilinearProperOpenMatePasting` as abbreviations of the
`VaryingRing` operations. The independent review (2026-10-24) withdrew the proposal.
The modules below compile against the published item but fail against the proposed
definitions. None of them is a file of the delivery.

- `Sheaf.Paper.FiniteFreeSystemRestriction` (unclaimed), line 135: its `simpa` expects
  `transition` to unfold to `constantSheaf.map (τ n)`. It now meets the def
  `VaryingRing.coefficientTransition`.
- `Sheaf.Paper.SemilinearCompactSupportCoefficientTransport` (F1), line 227: its witness
  types `push` as `SheafOfModules.pushforward` of the forgotten `coefficientMap`.
  `VaryingRing.ringMap` is equal to that map, but not definitionally.
- `Sheaf.SixFunctors.SemilinearEvaluationRingSquare` (unclaimed), line 217:
  `attribute [local irreducible] push` fails on the new `abbrev push`.

The item is unchanged apart from the proof of `rhoJInv_isIso` and its private helpers.
No definition and no signature changes, and no user is affected.

## Old

The published definitions of `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`.

## New

Unchanged: the published definitions.

## Users

None affected: no definition or signature changes.

## Status

landed 20261024T190336-L-4029661 2026-10-24 (merge of deliver/M7/Sheaf.SixFunctors.SemilinearProperOpenMatePasting)
