## What changed

Restored the assigned quarantined module
`Sheaf.AlgebraicGeometry.SelfProductRightAdjointBaseChangeLocal` from its archive.
Replaced its public import of the empty withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback`
with `WeilConjectures.AlgebraicGeometry.DerivedPullback`, the adopted source that defines
the functor used in the public statement. Added the missing module docstring.
The archived theorem signature, declaration docstring and complete proof are preserved.
The node retains its attachment and all four mathematical proof dependencies; its first
step now names the actual adopted source module used by `import all`.

Change record: `coord/changes/W7-self-product-right-adjoint-base-change-restoration.md`.

## Proved and sorry left

This is a zero-hole quarantine repair, not a new hole closure.
`AlgebraicGeometry.proper_flat_selfProduct_rightAdjoint_baseChange_local` already had
zero direct holes in the archive. Holes closed: 0 of 0. Holes added: 0.
Sorries left in delivered modules: none. No statements were split off.
The restored module compiled cleanly through `lcompile.py` in 10.2 seconds.
The proof continues to use the existing proper-flat base-change theorem after
standardizing the three specified localizations and transporting its isomorphism back.

## No longer needed

Removed the ineffective import `Sheaf.AlgebraicGeometry.DerivedPullback`, which is now an
empty withdrawn module; replaced it by its adopted source interface.
No mathematical node or dependency is pruned: the four planned dependencies are used.
No module is withdrawn; the quarantine archive is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic brief mentions proving sorries, but this assigned rework item has zero holes.
Its recorded defect is real: the archived first import no longer provides
`derivedPullback`, required by the public theorem statement. Restoring that statement
requires a public import of the adopted source interface.
The DAG's first proof step still named the former Sheaf path for
`DerivedPullbackOpenRestrictionUniverses`; the archived proof already imported the
WeilConjectures module. Corrected that path without changing the proof route.
No target, hypothesis, conclusion, or definition changed. The original unit route stays.

Searches: Loogle `"rightAdjointUniq"` found the standard uniqueness API; LeanFinder on
transport of proper-flat right-adjoint base change found only generic localization and
derivability tools; the msearch grep query `proper_flat_selfProduct|pullback_transport`
found no Mathlib match. Direct searches of the source and Sheaf libraries located the
existing transport proof and its four dependencies, so none was duplicated.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
