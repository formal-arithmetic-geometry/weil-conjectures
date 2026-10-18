# Sheaf.RingTheory.FinitelyPresentedSupportComplement imports

## Reason

The proof no longer needs the original determinant and adjugate imports directly; those
are encapsulated by the new intermediate theorem. The public Scheme import is retained.

## Old

`import WeilConjectures.LinearAlgebra.Matrix.CauchyBinet`
`import Mathlib.LinearAlgebra.Matrix.Adjugate`

## New

`import Sheaf.RingTheory.FinitelyPresentedSupportIdeal`

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.FinitelyPresentedSupportComplement | M9 | proof-only import replacement |

## Status

landed 20261018T071204-L-1672483 2026-10-18 (merge of deliver/M9/Sheaf.RingTheory.FinitelyPresentedSupportComplement)
