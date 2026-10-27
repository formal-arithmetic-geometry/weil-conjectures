## What changed

Added two named intermediate theorem declarations to
`Sheaf.Paper.DiagonalUniformizerScalarSquares` and proved the assigned theorem
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonal_uniformizer_scalar_squares`
by assembling them. The intermediate declarations isolate normalized square
existence and pointwise mate invertibility; each remaining proof is an explicit
named `sorry`.

## Proved and sorry left

The original theorem `diagonal_uniformizer_scalar_squares` is proved. Two strictly
smaller holes remain: `diagonal_uniformizer_restriction_square` and
`diagonal_uniformizer_restriction_mate_isIso`. They are represented by the new
DAG nodes listed below. No definitions contain `sorry`.

## No longer needed

No imports were removed. The original proof dependencies are used by the two
split theorem interfaces and remain recorded in their nodes.

## Where the brief, the DAG or earlier work was wrong

The original three-step plan bundled two independent constructions into one
unproved declaration. The Lean target can be reduced cleanly only after naming
square existence and mate invertibility separately; the target proof now consists
of the genuine categorical assembly of those components.

## New nodes

- `lem-diagonal-uniformizer-restriction-square`, for the normalized square
  construction.
- `lem-diagonal-uniformizer-restriction-mate-isIso`, for invertibility of its
  scalar mate on every complex.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
