## What changed

Replaced the single `sorry` in `LinearMap.power_spectrum_conjugation` with a proof
using the existing upper triangular basis theorem, Mathlib's triangular characteristic
polynomial formula, multiset root identities, and coefficientwise conjugation.
The real polynomial is constructed explicitly from the real parts of the finitely
supported coefficients. Updated the item's DAG proof to match this route.
No statement, definition, or public import changed; no consumer adaptation is needed.

## Proved and sorry left

Closed: `LinearMap.power_spectrum_conjugation`
(node `lem-zl-power-spectrum-conjugation`), one original hole.
Added: none. Remaining holes: none. No decomposition or new declarations.

## No longer needed

Removed the private direct import `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`.
The proof no longer needs `lem-weil-pbc-block-triangular-determinant`: Mathlib already
proves `Matrix.charpoly_of_isUpperTriangular`, so no new block determinant induction is
necessary. Its Mathlib module remains available transitively through triangularization;
no library module is withdrawn. The retained dependency `p-linear-triangular` supplies
the existing proved `Module.End.exists_basis_isUpperTriangular_toMatrix`.
Added only the private proof import `WeilConjectures.Mathlib.Algebra.Polynomial.Reverse`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was wrong. The DAG planned to reconstruct an adapted basis
and determinant products, although the source library already supplies the triangular
basis and Mathlib supplies the triangular characteristic polynomial. Directly mapping
multiset equalities replaces the planned explicit occurrence permutation. Root counts
handle collisions without a separability assumption. Empty index sets, zero diagonal
entries, repeated eigenvalues, and characteristic dividing the exponent all remain
covered by the proof; it uses no inversion or diagonalizability.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
