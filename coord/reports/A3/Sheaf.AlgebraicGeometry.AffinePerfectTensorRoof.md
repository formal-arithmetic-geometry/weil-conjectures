## What changed

Restored Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof from its rework assignment
as a public re-export of the existing proved upstream module
WeilConjectures.AlgebraicGeometry.AffinePerfectTensorRoof. Updated
lem-sc-affine-perfect-tensor-roof's Lean attachment to that canonical declaration.
The quarantine archive, upstream source, mathematical statement, proof steps,
proof dependencies, proof origin and unit route are preserved.

The archived and upstream signatures are textually identical after the K-flat
predicate rename IsAcyclicTensorKFlat → IsKFlatTensor; the two predicates have
identical bodies. A scratch consumer imports only the restored path, reconstructs
the archived predicate privately, and proves the full archived statement by the
canonical theorem. It compiles in 6.5 seconds. Both it and the canonical theorem
have only propext, Classical.choice and Quot.sound as axioms. The restored module
compiles in 1.4 seconds. A scratch copy of the actual parent
WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift, changing only its private
roof import to the restored Sheaf path, compiles in 12.8 seconds. Scratch checks
are retained in scratchpad and are not delivery modules.

Change record: coord/changes/affine-perfect-tensor-roof-upstream-restoration.md.
No other module requires adaptation. No target statement or definition changes.

## Proved and sorry left

This is a zero-hole quarantine repair: 0 original holes, 0 holes closed,
0 holes added, 0 split off, and 0 holes remaining in the item.
AlgebraicGeometry.Scheme.exists_affine_perfect_tensor_roof already has a complete
upstream proof with only the three permitted axioms; the restored import path
exposes that proof instead of duplicating its declaration. No decomposition or
new proof is claimed.

## No longer needed

The duplicate local private helper affinePerfectTensorRoof_aux and duplicate
local declaration of exists_affine_perfect_tensor_roof are replaced by the
canonical existing theorem, whose full proof remains unchanged upstream.
The archived direct public imports
WeilConjectures.AlgebraicGeometry.PerfectComplex,
Sheaf.AlgebraicGeometry.DerivedTensorAugmentation, and
Mathlib.AlgebraicGeometry.AffineScheme, and direct private imports
WeilConjectures.AlgebraicGeometry.RHomSupportedQuasiCoherentPerfectPart,
Sheaf.AlgebraicGeometry.AffineKoszulSectionRoof, and
Sheaf.AlgebraicGeometry.TensorRoofTransposition are replaced by the single
public import WeilConjectures.AlgebraicGeometry.AffinePerfectTensorRoof.
All mathematical proof dependencies remain needed through its existing proof;
no node or module is withdrawn or claimed pruned. No deleted.txt is used.

## Where the brief, the DAG or earlier work was wrong

The assigned source is quarantined, not withdrawn. Its recorded compiler failure
is a private-import visibility failure for IsAcyclicTensorKFlat. The upstream
sync already adopted the same theorem, using the definitionally identical name
IsKFlatTensor. The old node attachment still points at the quarantined duplicate.
Restoring it as a canonical re-export repairs the import path and attachment
without recreating the mixed duplicate environment. The proof plan and its
three stated dependencies were correct and remain in place.

Current sources and the quarantine contain no import of the old Sheaf path.
The sole theorem application is the upstream AffinePerfectMapLift, which was
checked through the restored path without delivering any source-library edits.
The parent DAG dependency remains intact; this is restoration, not pruning.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
