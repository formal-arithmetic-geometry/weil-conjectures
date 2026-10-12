# isRegularRing_quotient_X_pow_sub_of_isUnit_derivation

## Reason

The proof is now implemented using Mathlib's coefficientwise derivation and polynomial
regularity theorem. The public theorem signature is unchanged; this record documents the
proof dependency/interface review requested by the delivery checks.

## Old

`theorem isRegularRing_quotient_X_pow_sub_of_isUnit_derivation (R : Type u) [CommRing R] [IsRegularRing R] (f : R) (D : Derivation ℤ R R) (hDf : IsUnit (D f)) (n : ℕ) (hn : 1 ≤ n) : IsRegularRing (Polynomial R ⧸ Ideal.span ({Polynomial.X ^ n - Polynomial.C f} : Set (Polynomial R)))`

## New

The same signature, with a complete proof.

## Users

| module | group holding it | effect |
|---|---|---|
| downstream importers | unclaimed | theorem remains definitionally unchanged |

## Status

landed 20261012T184239-L-3994470 2026-10-12 (merge of deliver/A2/Sheaf.AlgebraicGeometry.DegreePExtensionRegular)
