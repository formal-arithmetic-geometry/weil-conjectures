## What changed

Proved `AlgebraicGeometry.Etale.properOpen_coefficient_mate` in
`lean/Sheaf/Paper/ProperOpenCoefficientMate.lean`.  The proof reduces the coefficient
square to injectivity of the inverse proper direct-image adjunction Hom-equivalence.
The remaining mate-pasting calculation is recorded as the strictly weaker theorem
`AlgebraicGeometry.Etale.properOpen_coefficient_mate_transposed` in the same module.
The item node now records this dependency and the new split node.

## Proved and sorry left

Closed the original `properOpen_coefficient_mate` sorry (1 hole).  One new sorry remains,
`properOpen_coefficient_mate_transposed`, with node
`lem-sp-proper-open-coefficient-mate-transposed`; it is the transposed mate identity
whose injectivity proof closes the original target.

## No longer needed

None.  Every existing import and dependency remains used by the declarations and
naturality proofs in the module.

## Where the brief, the DAG or earlier work was wrong

No error found.  The existing DAG proof plan correctly identifies the coefficient
mate-pasting step; the delivery makes its transpose explicit so that the target proof
is a real Lean reduction.

## New nodes

Added `lem-sp-proper-open-coefficient-mate-transposed` in
`dag/nodes/sec-smooth-purity/`.  Its declaration is the inverse-adjunction transpose
of the coefficient interchange/composite equality.  Its proof source is the Step 1
mate-pasting argument of `lem-sp-proper-open-coefficient-mate` (Stacks tags 0F7B and
0GL6).  The target theorem follows from this helper by injectivity of the adjunction
Hom-equivalence; the helper is strictly weaker than the target and is not a renamed
copy of it.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
