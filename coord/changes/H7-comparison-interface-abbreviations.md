# SheafOfModules comparison-data interfaces (withdrawn)

## Reason

The delivery 97d77654d428 of
`Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses` (group H7) also changed
the unclaimed module `Sheaf.Paper.RingedTopoiTensorComparisonData`. It bound
`[J.HasSheafCompose (forget₂ CommRingCat RingCat)]` explicitly in four variable
blocks. It also turned `RingedComparisonInsertion`, `RingedComparisonTensor`,
`ringedComparisonNaturality`, `ringedComparisonInsertionCondition` and
`ringedComparisonPureCondition` from `def` into `abbrev`.

The reviewer (2026-10-26) withdrew this change. The module stays exactly as published.

- The change was not needed. The delivered item
  `Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses` compiles unchanged
  against the published `RingedTopoiTensorComparisonData` (lcompile, 46-49 s). Its six
  direct importers then compile as they do against the published library.
- The change broke three direct importers that compile against the published library
  (each compiles there: 47 s, 42 s, 31 s):
  - `Sheaf.AlgebraicGeometry.ProEtaleInverseImageScalarUnitNormalization` broke
    with an argument type mismatch at `CanonicalRingedTensorComparisonOnSmallSites … ho`,
    with universes forced to 0, and then `normalizedHom` unknown.
  - `Sheaf.Paper.RingedTensorAdjunctionMate` broke at line 455 with "failed to solve
    universe constraint".
  - `Sheaf.SecSmoothPurity.CoefficientComparisonsBalancedConstruction` broke at line 146
    with `RingedComparisonTensor ?R ?S (extensionFunctor i)`, with universes forced to 0.

  The new instance binders come before the explicit arguments. They change how
  universes and implicit arguments are elaborated at partial applications.

## Old

The published `lean/Sheaf/Paper/RingedTopoiTensorComparisonData.lean`.

## New

The same: no change.

## Users

None affected; nothing changes.

## Status

withdrawn
