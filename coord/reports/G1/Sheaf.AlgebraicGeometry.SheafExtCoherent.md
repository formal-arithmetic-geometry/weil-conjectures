## What changed

Restored the quarantined module `Sheaf.AlgebraicGeometry.SheafExtCoherent` from
`quarantine/Sheaf/AlgebraicGeometry/SheafExtCoherent.lean`, preserving its theorem signature.
Made `WeilConjectures.AlgebraicGeometry.Coherent` a public import, since the exported
signature names `RingedSpace.IsCoherent`.

Proved `AlgebraicGeometry.sheafExt_isCoherent` by local finite free resolutions,
the bounded-above finite free derived Hom model, and coherent kernel/cokernel closure.
The private resolution helper uses the source construction with local Noetherianity
only. The private Hom comparison uses the source scalar comparison with arbitrary
coefficient G. No source-library module is edited. Updated the node to the actual route.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.sheafExt_isCoherent`
(node `lem-sc-sheaf-ext-coherent`). Added zero holes. No sorry remains in the delivery.
All four private helpers have complete proofs. No split-off theorem or new axiom.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.AffineRHomQuasiCoherent`,
`Sheaf.Paper.DerivedInternalHomRestrictOpen`,
`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`, and
`Sheaf.AlgebraicGeometry.CoherentFiniteType`.

The route does not use `lem-sc-affine-rhom-qcoherent` or `lem-sc-ext-noetherian-finite`:
coherence follows directly from finite direct sums and kernels/cokernels of coherent
sheaves. It uses ordinary Hom restriction and K-injective preservation instead of
`lem-sc-derived-internal-hom-restrict-open`. The affine finite-type criterion
`lem-weil-pbc-quasi-coherent-finite-type-affine` is unnecessary because finite generators
and the affine counit directly prove finiteness of the affine module.
`pqf-def-coherent` remains a statement dependency; its quasi-coherent-finite-type
abbreviation is unnecessary in the proof. Removed its obsolete affine finite-type
tool approval from this node. No module is withdrawn: other parents may still need them.
The unit's own statement and realized steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The current item source is quarantined, not withdrawn; the rework row was checked before
restoring it. The archived file fails with unknown `RingedSpace.IsCoherent` in its public
signature because its defining import was private. The public import repair fixes this.
The existing affine-resolution theorem assumes a globally Noetherian scheme, although its
construction only uses local Noetherianity. Its signature is preserved; this delivery
uses a private version of that construction. The existing scalar Hom comparison is
specialized to the structure module; the same proof works for the arbitrary target G.
The old affine Ext detour is unnecessary for this degree-zero special case.

Change record: `coord/changes/G1-sheaf-ext-coherent-restoration.md`.
The only textually found direct consumer is the quarantined
`Sheaf.AlgebraicGeometry.ExtSupportCohomologyVanishing`; its interface is preserved.
The downstream script does not index this absent item and reports unknown module.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
