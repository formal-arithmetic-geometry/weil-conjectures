## What changed

Restored `lean/Sheaf/SixFunctors/FlatModel.lean` from its assigned quarantine source.
Replaced its three obsolete `LocallyClosedStratification` references with the current
`Scheme.Stratification`, removed the retired empty stratification import, and inferred
the local locally-bijective instance at its explicit coefficient universe. All five
public theorem proofs and both generator constructions are retained. Updated the
existing node's Lean note and proof-origin restoration note; no proof edge changes.

The unmodified archive failed on the obsolete names. The repaired complete module
compiled through lcompile.py with exit code 0 and no warnings. There are no live
consumers; the two quarantined direct consumers were inspected for API compatibility.
The change record is `coord/changes/G4-flat-model-restoration.md`.

## Proved and sorry left

This is a zero-hole restoration/repair, not a proof-count increase. The archive has
zero textual sorries; the delivery has zero textual sorries. Holes closed: none.
Holes added or split off: none. No holed statement was changed or withdrawn.

Retained and compiled the complete proofs of `AlgebraicGeometry.proEtaleFlatModel`,
`AlgebraicGeometry.proEtaleFlatStratification`,
`AlgebraicGeometry.etaleThickGeneration`,
`AlgebraicGeometry.proEtaleThickGeneration`, and
`AlgebraicGeometry.proEtaleThickGeneration_eq`, attached to
`sk-lem-sf-flat-model`. Every private helper is also proved.

## No longer needed

Removed the public import `Sheaf.AlgebraicGeometry.LocallyClosedStratification`, which
is already a withdrawn empty module. The current upstream stratification interface is
provided by existing imports. No mathematical dependency node, proof step, Lean
attachment, or parent obligation is pruned; no module is withdrawn by this delivery.

## Where the brief, the DAG or earlier work was wrong

The assigned live module is absent, with the complete zero-hole version preserved at
the rework row's quarantine path. Its old interface refers to a retired stratification
name and an integral-coefficient instance no longer imported. These are compatibility
errors, not missing mathematical proofs. Current intrinsic constructibility and
FlatModelGeneration already use Scheme.Stratification. The recorded unit route and
all mathematical conclusions are preserved, including the empty scheme and zero ring.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
