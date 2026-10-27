## What changed

Proved `AlgebraicGeometry.ProEtale.PurityTransport.finiteLiftAnnihilator` in
`Sheaf.SecSmoothPurity.TransportFiniteLines`. Apply injectivity of `ULift.ringEquiv` and simplify its preservation of
natural casts, powers, and zero, using `Nat.cast_pow` to recover the given
annihilator equation. All declaration signatures and definitions are unchanged; the existing prime
instance is referenced explicitly to retain the interface without a linter warning.
The argument works also for the zero ring and for n = 0; no finiteness or
nontriviality assumption is needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.PurityTransport.finiteLiftAnnihilator`
(node `def-pur-transport-finite-line-coordinates`). Zero holes remain in the
item module; zero holes were added and no statements were split off.

## No longer needed

None. All four existing public imports remain needed by the finite encoding,
root comparison, Cartier line and normalization interfaces. The node has no
proof dependencies or proof steps to prune; its statement dependencies remain
needed by the unchanged definitions. No modules or nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

None. The coefficient-size argument is elementary: natural-number casts and
zero commute with the universe lift. Mathlib search confirmed
`ULift.down_natCast`; the proof uses the existing Mathlib interface directly.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
