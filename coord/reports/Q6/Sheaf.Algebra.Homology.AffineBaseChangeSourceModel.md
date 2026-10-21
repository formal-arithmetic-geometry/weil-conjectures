## What changed

Retire the quarantined module
`Sheaf.Algebra.Homology.AffineBaseChangeSourceModel` in favour of the existing proved
`WeilConjectures.Algebra.Homology.AffineBaseChangeSourceModel`. The original path is
listed in deleted.txt. The quarantine archive is unchanged. The node
lem-pc-affine-base-change-source-model now names the official provider and its
current signature; its statement, proof plan, dependencies and unit route stay.

The historical consumer Sheaf.Algebra.Homology.AffineBaseChangeCohomologyModel is
already absent from both lean/ and quarantine/. Its node already names the official
cohomology-model module, which imports the official source model and uses its API.
There is no remaining live importer to adapt. No adopted source or target changes.

Change record: coord/changes/Q6-affine-source-model-canonical-reexport.md.

Validation: lcompile.py compiled the unchanged official cohomology-model consumer
in 36.2 seconds and the full archived-signature compatibility probe in 16.0 seconds,
both with exit code 0. The probe imports the official source model directly, applies
its theorem to every original argument, and checks that the K-flat predicates are
equal by rfl. Both theorem versions print only propext, Classical.choice and
Quot.sound as axioms. A direct scan of current Lean and quarantine sources found
zero imports of the retired Sheaf path. These probes remain only in scratchpad/
and are not delivered. The downstream tool cannot index the absent quarantined
module; the direct source scan and actual DAG-parent check cover its users.

## Proved and sorry left

Zero-hole retirement and rework: the quarantined item already has zero holes.
Holes closed: none (0 of 0). Holes added: none (0). Sorries left: none.
No split-off theorem. AlgebraicGeometry.exists_affineBaseChangeSourceModel remains
proved at its official provider, attached to lem-pc-affine-base-change-source-model.

## No longer needed

Retired module: Sheaf.Algebra.Homology.AffineBaseChangeSourceModel. Its duplicate
theorem and the previous attempt's compatibility re-export are unnecessary.
The six private proof imports of the quarantined copy are removed with it:
WeilConjectures.Algebra.Homology.AffineBaseChangeTildeSourceModel,
Sheaf.Algebra.Homology.AffineBaseChangeSourceRepresentativeIso,
WeilConjectures.Algebra.Homology.RingTensorCohomology,
Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde,
Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition (import all), and
WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore.
The official theorem continues to use the corresponding official proof modules.
The copy's three public imports are supplied by the official provider. The
previous attempt's additional Sheaf.Algebra.Homology.KFlat public import is also
unnecessary. No mathematical node or proof dependency is pruned: all six original
proof dependencies and the cohomology-model parent's dependency remain needed.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined after a failed cluster restore, not mathematically
withdrawn. Retirement is explicitly authorized by the later RETIRE assignment and
hand-off, and preserves its theorem via the official twin. The previous attempt's
re-export restored a historical path instead of retiring it; this packet corrects
that mismatch. The listed historical Sheaf consumer has already been retired.

The twin's API difference is the definitionally equal IsKFlatTensor spelling in
place of IsAcyclicTensorKFlat. The official cohomology-model consumer already uses
that API. The node's old Lean attachment still named the quarantined provider;
this packet reconciles the attachment, preserving the actual parent dependency.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
