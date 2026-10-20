## What changed

Restored `lean/Sheaf/AlgebraicGeometry/KFlatStalkResidueCohomology.lean` from its
recorded quarantine archive. Updated the K-flat hypothesis of
`AlgebraicGeometry.Scheme.nonempty_kFlat_stalk_residueCohomology_linearEquiv` from
the obsolete `CochainComplex.IsAcyclicTensorKFlat` to upstream
`CochainComplex.IsKFlatTensor`. The predicates express the same acyclic-total-tensor
condition. The existing proof and its three declared mathematical dependencies are
preserved: compute derived pullback on P, commute one-point evaluation with homology,
and apply the residue pullback/stalk natural isomorphism.

Updated the node's Lean signature to match. Change record:
`coord/changes/F4-kflat-stalk-residue-upstream-predicate.md`.
Remote single-file compilation passes without warnings in 12.3 seconds.

## Proved and sorry left

This is a zero-hole quarantine repair. The existing complete proof of
`AlgebraicGeometry.Scheme.nonempty_kFlat_stalk_residueCohomology_linearEquiv` is
restored and compiles. Original holes: 0. Holes closed: 0. Holes added: 0.
Holes left: 0. Split-off statements: 0.

## No longer needed

Removed the private proof import `Sheaf.Paper.DerivedHomMayerVietoris`; no declaration
from it is used by the proof. This is a re-export of the unrelated upstream
Mayer-Vietoris module. No DAG proof dependency is pruned: all three dependencies
listed by `lem-sc-kflat-stalk-residue-cohomology` are still used. No module is
withdrawn and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The item has no sorry to close: its rework row records the unknown old K-flat name,
and the archive already contains a complete proof. This delivery repairs that actual
compiler error instead of moving any hole. The node's recorded Lean signature used
the same obsolete spelling and is refreshed. Mathematical statement, arbitrary
integer degree, universes, representatives, residue field action and unit route are
preserved. Zero complexes and unbounded complexes require no extra assumptions.
The three direct consumers are quarantined separately; the base-change consumer also has an obsolete explicit K-flat
annotation, independent of this item. Their theorem call arguments and
conclusions need no change from this API rename.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
