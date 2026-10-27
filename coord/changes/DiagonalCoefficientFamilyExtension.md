# Change record: DiagonalCoefficientFamilyExtension

The delivery touches the B2-held module `Sheaf.AlgebraicGeometry.SfP1ChartExchange`
(lean/Sheaf/AlgebraicGeometry/SfP1ChartExchange.lean). The change is whitespace only:
in the private theorem `shiftedLine_comp` the final `simp (config := { dsimp := false }) only [...]`
list is broken after its opening bracket (one line split into two). No token, declaration,
signature, import, attribute or interface changes.

The worker's original reason (three `unusedSimpArgs` warnings for `ordinaryFinitePullback`,
`ordinaryFiniteLine`, `ordinaryFiniteDegreeZero` in that `simp only`) was already repaired on
the published library by the maintenance commit 542e0ba ("retain SfP1ChartExchange warning
repair after recovery build"); the delivered file is the published one plus the line break.
The change is therefore NOT FORCED by this item. It has no effect on any user
(importers: Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransport,
Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportFalse,
Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue; current holder B2).

The item module `Sheaf.Paper.DiagonalCoefficientFamilyExtension` keeps its public statement
and its public import; it adds two plain (non-public) imports
`Sheaf.Paper.DiagonalCoefficientFiniteExtension` and `Sheaf.Paper.DiagonalCoefficientFiniteClosure`.
Its only importer, `Sheaf.Paper.DiagonalTowerCoefficients`, compiles unchanged.
