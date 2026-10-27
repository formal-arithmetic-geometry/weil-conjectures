# ordinaryFiniteShiftedLinePullback_square

## Reason

Repair the landing return for fd5306fe8ed. Main already provides this square
in `FiniteShiftedLineSquare`, including the zero-modulus case. The packet's
positive-modulus copy is redundant and collides under the same public name.

## Old

`OrdinaryFiniteTwistComposition` declared a second
`ordinaryFiniteShiftedLinePullback_square` with an additional `hN : 0 < N`
argument. `OrdinaryFiniteDiagonalTraceCoordinates` imported that module and
supplied `hN` when applying the square.

## New

Remove the duplicate declaration entirely. TraceCoordinates privately imports
`Sheaf.AlgebraicGeometry.FiniteShiftedLineSquare` and calls its existing theorem
as `ordinaryFiniteShiftedLinePullback_square A N hA t`. The two intermediate
invertibility arguments agree in this application, since both schemes are
`ProjectiveLine S`. All public TraceCoordinates signatures remain unchanged.
The TwistComposition node now attaches only its three composition lemmas;
TraceCoordinates uses `lem-asd-finite-shifted-line-square` directly. The
composition lemmas remain needed by ChartExchange.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistComposition` | Z8 | Remove the redundant declaration; retain the three composition lemmas. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalTraceCoordinates` | Z8 | Import the existing square and omit the positivity argument. |
| `Sheaf.AlgebraicGeometry.OrdinaryFiniteDiagonalChartExchange` | Z8 | Unchanged; still uses the named-composite composition theorem. |

The unchanged existing square module compiles against the packet in 10.6 seconds.
Its temporary source copy was removed after this check. No current source file or
existing square node is changed. Earlier F1 and X7
repairs are retained; their seven recorded source hashes still match current main.

## Status

landed 20261027T135451-L-3711227 2026-10-27 (merge of deliver/Z8/Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalUnit)
