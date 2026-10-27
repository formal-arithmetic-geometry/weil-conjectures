## What changed

Filled `AlgebraicGeometry.ProEtale.PurityTransport.linePullCoordinates_nonempty`
in `Sheaf.SecSmoothPurity.TransportLinePull`. Obtain the projection-normalized
integral comparison from `integralComparison`, extend it with `scalarPull`, and
use `powerPull` for every nonnegative tensor power. An induction identifies the
recursive coefficient lines with the `Nat.rec`
expressions expected by `powerPull`; rewriting both endpoints then proves
heterogeneous normalization by reflexivity. All signatures, definitions, and
imports are unchanged. Recorded these steps and their existing dependencies in
`def-pur-transport-line-pullback`. The final single-file compile passed in 9.5 s
with no errors or warnings.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.PurityTransport.linePullCoordinates_nonempty`.
Zero holes remain in the delivered module; zero holes added or split off.
The proof uses the already stated, still unproved `integralComparison`
(`def-pur-transport-canonical-pullback`); this delivery does not prove that dependency.

## No longer needed

None. The original public import `Sheaf.SecSmoothPurity.TransportDerived`
is needed for the public derived-coordinate definition and already exposes the
integral, scalar, and tensor-power interfaces. No imports were added or removed.
The node originally had no proof dependencies to prune. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The coefficient-line recursion and the
`Nat.rec` recursion in `powerPull` require a proved equality, rather than
definitional reduction; the local induction supplies it. The existing node had an empty proof
array despite its existence theorem; it now records the actual construction.
The zeroth power is included by the inverse unit tensorator of `powerPull`,
without choosing a root frame. Searches through Lean Finder, Loogle, and the
source trees confirmed the existing project interfaces provide the direct route.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
