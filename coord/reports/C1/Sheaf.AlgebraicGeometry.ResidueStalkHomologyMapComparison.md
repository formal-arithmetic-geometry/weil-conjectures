## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ResidueStalkHomologyMapComparison.lean` from its
quarantine path. The theorem `AlgebraicGeometry.isIso_residue_stalk_homologyMap` and its
complete proof are unchanged from the previously landed proof. The forced repair changes
its public proof dependency from the withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback`
module to `WeilConjectures.AlgebraicGeometry.DerivedPullback`, which is the adopted source
module that provides `derivedPullback` on the current base. No declarations or statements
were changed.

## Proved and sorry left

The existing theorem `AlgebraicGeometry.isIso_residue_stalk_homologyMap` remains proved,
with zero `sorry`s in the restored module. No new declarations or holes were added.

## No longer needed

The withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback` import is no longer used. The
upstream `WeilConjectures.AlgebraicGeometry.DerivedPullback` import is required by the
public theorem signature and supplies the current `derivedPullback` declaration. No DAG
proof dependency or unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

The upstream sync quarantined this module because its old import pair referenced a
Sheaf copy of `DerivedPullback` while the adopted source tree already supplied the same
`AlgebraicGeometry.derivedPullback` declaration. The quarantine diagnostic therefore
reported an environment name collision. The current Sheaf copy is a withdrawn stub, so
restoring the proof requires the upstream public import. The theorem statement and proof
remain valid and compile on the current base.

The import-interface repair is recorded in
`coord/changes/C1-residue-stalk-homology-derived-pullback-import.md`.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
