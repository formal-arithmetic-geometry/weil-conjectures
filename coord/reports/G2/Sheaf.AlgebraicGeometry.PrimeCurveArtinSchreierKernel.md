## What changed

Restored `Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel` from its recorded
quarantine path. Migrated the two retired forwarding imports to the corresponding
canonical `WeilConjectures` modules, preserving their public/private visibility.
The migration is recorded in
`coord/changes/G2-prime-curve-artin-schreier-restoration.md`.
Every other byte of the quarantined Lean source is unchanged. The node is retained
unchanged, including its Lean attachment, proof plan and dependency edges.

This is the assigned upstream-sync rework, whose instructions explicitly permit
retaining the original hole. The earlier proof draft is preserved separately in
the sandbox; its full-file compilation exceeded the server's 60-second limit.
It is not part of this delivery and no proof completion is claimed.

## Proved and sorry left

Closed zero of the one original holes. Added zero holes. The original named theorem
`AlgebraicGeometry.Etale.exists_prime_curve_artinSchreier_kernel` retains its single
`:= by sorry`, source and complete natural-language proof. No definition contains
a hole, no statement changes and no result is split off.

The restored file is checked by the project compile server and delivery preflight.
Its public theorem signature and body match the quarantined original exactly.

## No longer needed

The retired forwarding imports
`Sheaf.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison` and
`Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf` are replaced by the same
upstream providers they formerly re-exported. These are import migrations, not
mathematical dependency pruning. No node, module or unit route is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The active source is absent because it was quarantined by the upstream sync.
Both former forwarding modules were subsequently retired. Their retirement change
records explicitly preserve this archive for migration when restored. Replacing
those imports is the necessary build repair. The previous sandbox report claimed
a completed proof before successful full-file compilation; this report corrects
that claim. No downstream declaration use needs adaptation because every public
declaration and visibility is preserved.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
