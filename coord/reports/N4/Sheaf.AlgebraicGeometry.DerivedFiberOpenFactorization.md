## What changed

Restored lean/Sheaf/AlgebraicGeometry/DerivedFiberOpenFactorization.lean from its
coord/rework.tsv quarantine source. Replaced its private proof import
`import all Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde` with
`import all WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`.
The retired Sheaf module is empty; the canonical upstream module provides the
proved private pullbackOpenIso and pullbackCompIso helpers used by the proof.
Every other line is identical to the archive. All public imports, signatures,
definition bodies, attributes and proofs are preserved.

The existing argument factors the residue morphism through the open, compares
exact derived restriction with open pullback, composes derived pullbacks, and
whiskers with homology and residue-field sections. No new mathematical input or
unit-route change is involved. The existing node's Lean attachment and proof
dependencies remain correct, so no node edit is needed.

Compiled the restored module through lcompile.py in 14.7 seconds, with no errors
or warnings. Checked both quarantined consumers: the public API they use is
unchanged, so this repair forces no adaptation. The restoration change record is
coord/changes/n4-derived-fiber-open-factorization-restore.md.

## Proved and sorry left

This is a zero-hole rework assignment. The archive and repaired module both have
zero sorry occurrences. Holes closed: none. Holes added or split off: none.

The existing complete proofs remain for
AlgebraicGeometry.Scheme.openResiduePoint_comp,
AlgebraicGeometry.Scheme.localDerivedFiberCohomologyFunctor_eq, and
AlgebraicGeometry.Scheme.derived_fiber_open_factorization
(node new-derived-fiber-open-factorization). The two data definitions contain no
holes. The assigned unknown-identifier failure is repaired.

## No longer needed

Removed the private proof import of the retired empty module
Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde, replacing it with its
canonical upstream implementation. No mathematical node or module is withdrawn:
lem-pc-affine-derived-pullback-tensor-tilde remains needed and already points to
WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde. The item and
its dependencies are preserved, including the needs of its quarantined parents.
No other imports are removed.

## Where the brief, the DAG or earlier work was wrong

The assigned module is absent from lean/ because it is quarantined, not because
it is unnecessary. Its archived proof import still names a Sheaf twin retired
after the upstream sync. This left pullbackOpenIso and pullbackCompIso unavailable.
The canonical upstream implementation has the required proved helpers; switching
the private import fixes the defect without changing a statement or definition.
The DAG's current upstream attachment is already correct.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
