## What changed

Added the twist/local-inverse component square in
`Sheaf.Paper.DiagonalDncEtaleNaturalityTwist` and used it to assemble the
four-factor identity in `Sheaf.Paper.DiagonalDncEtaleNaturality`. The assembly
is by cancellation of the canonical dualizing comparison and the inverse of
`T.map (νU.map b)`. The item imports the component module as a proof-only
import.

## Proved and sorry left

The main declaration `diagonalDncEtaleNaturality` is reduced to the component
square and its categorical cancellation. The new component declaration
`diagonalDncEtaleNaturality_twist` remains a split proof obligation, with node
`lem-pur-diagonal-dnc-etale-naturality-twist-square`.

## No longer needed

The original lower proof dependencies other than the component square are no
longer imported directly by the item module; the component node records the
geometric DNC dependencies it uses. No existing library module was removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof bundled the twist, local-inverse, and dualizing locality
squares into one equality. Separating the twist square from the final
invertible cancellation is required for a typed Lean assembly because the
coefficient pullback is definitionally the affine-linear base coefficient.

## New nodes

`lem-pur-diagonal-dnc-etale-naturality-twist-square` records the strictly
smaller twist/local-inverse component square and is stated by
`Sheaf.Paper.DiagonalDncEtaleNaturalityTwist`.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
