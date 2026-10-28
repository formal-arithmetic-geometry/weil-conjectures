# Integral normalized family rework repair

The module was quarantined after the `DiagonalTrace.IsDiagonalLimit` definition
changed so its finite-cycle clause was no longer definitionally equal to the
presentation emitted by `diagonalTower_limit`. The repaired private conversion now
unfolds `DiagonalCompletedLimitSpec` and the four irreducible normalization names
before applying the existential rearrangement. Public declarations and imports remain
unchanged; the module has zero `sorry` holes.
