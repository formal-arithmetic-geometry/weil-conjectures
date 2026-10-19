## What changed

Replaced the two theorem holes in `Sheaf.Paper.RealSheavesSetup` with proofs.
`RealSheaves.Setup.ringChar_eq` uses `FiniteField.card`, divisibility of a prime
power, and equality of primes dividing one another. `RealSheaves.Setup.openIsCurve`
restricts each finite chain of irreducible closed subsets to an irreducible component.
Pure dimension one then bounds its length. Dimension decreases under the open
embedding. Local Noetherianity and compactness of the original finite-type scheme
give Noetherianity, so the open structure morphism is quasi-compact; separatedness
and local finite type restrict by composition. Added the proof-only import
`Mathlib.AlgebraicGeometry.Noetherian`.

All existing signatures, definitions, public imports and docstrings are unchanged.
The setup node is a definition with no planned proof steps; its recorded elementary
characteristic and open-curve interfaces are proved directly from Mathlib.

The resumed session confirmed that both proof bodies compile through `lcompile.py`.
The first delivery dry run also typechecked both proofs and reported an unused-binder
warning. The proof now explicitly eliminates the given nonemptiness witness while
preserving the existing signature. The final delivery dry run passed compilation,
axiom checks and preflight, with review class AUTO and no warnings.

## Proved and sorry left

Closed both original holes:
`RealSheaves.Setup.ringChar_eq` and `RealSheaves.Setup.openIsCurve`
(both attached to `d-real-setup`). Both proof bodies have passed compiler verification.
No `sorry` remains in the sandbox module.
No holes, declarations, modules or nodes were added. This is intended as two proofs,
not a decomposition. No axiom or arbitrary existence witness is introduced.

## No longer needed

None. No original import was removed. All public imports support the existing
definitions or their interfaces. There were no original proof dependencies to prune,
and the unit has no proof steps that could be bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction to the statements or definitions was needed.
The open-curve proof does not require nonemptiness of the open, smoothness or
geometric connectedness, because the ordinary library curve predicate admits the
empty scheme; its existing signature is preserved. Restricting chains to their
containing component proves the required dimension bound even for reducible curves.
The earlier session's compile-server failures cleared on resumption; the compiler
has now returned Lean results for the preserved proofs.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
