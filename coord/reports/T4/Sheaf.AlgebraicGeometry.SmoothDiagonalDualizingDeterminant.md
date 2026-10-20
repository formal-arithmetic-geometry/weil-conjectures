## What changed

Restored `Sheaf.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant` from its rework
assignment as a compatibility module. It publicly imports the already proved upstream
`WeilConjectures.AlgebraicGeometry.SmoothDiagonalDualizingDeterminant` and the proved
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison`. It no longer redeclares the
upstream theorem or imports a withdrawn constant-rank comparison module.

Reattached `lem-sc-smooth-diagonal-dualizing-determinant` to the canonical upstream theorem.
All original DAG dependencies remain; the existing exterior-sheaf equality node is added
for the compatibility transport. The module's proved private `exteriorSheaf_compatibility`
checks the entire archived conclusion, including independent derived universes, by rewriting
the existing equality. The Stacks Tag 0BRT fourth-equality route remains unchanged.

Change record: `coord/changes/smooth-diagonal-dualizing-determinant-upstream.md`.

## Proved and sorry left

The archived item has zero direct sorries. Closed: none (0 of 0). Added: none.
Remaining direct sorries in the restored module: none.
The private theorem `AlgebraicGeometry.exteriorSheaf_compatibility` is completely proved
from `AlgebraicGeometry.smoothDiagonal_dualizing_determinant` and
`AlgebraicGeometry.Scheme.Modules.exteriorSheaf_eq_exteriorPower`.
This is a quarantine/interface repair, not a claim to have newly proved the upstream result.
No definition contains a hole and no axiom is introduced.

## No longer needed

No mathematical dependency or node is pruned. In particular the quarantined parent
`SmoothProperDualizingTensorEvaluation` and its citation of this node remain preserved.
The local copy of the regular-sequence/Koszul/constant-rank proof is replaced by the
existing canonical proof. Its proof-only imports of KoszulRegularImmersionDualizing,
SmoothDiagonalRegularGenerators, RegularSequenceKoszulRegular and
SmoothDiagonalIdealConormalRank are retained by that upstream theorem.
The obsolete import `Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison`
is replaced by the upstream theorem's canonical constant-rank comparison dependency.
No source-library declaration, signature, body, attribute or public import is changed.

## Where the brief, the DAG or earlier work was wrong

This item is a rework repair with zero direct holes, not a theorem still needing proof.
The current retirement inventory also lists this module as a twin of the canonical upstream
module (`twin restates smoothDiagonal_dualizing_determinant`). The rework row names a collision between the old and canonical locally ranked complex.
The archive also imports a now-empty Sheaf constant-rank comparison module. A complete,
canonical upstream theorem with the same declaration name already exists, differing only
in the exterior-sheaf implementation. An existing proved equality identifies those
implementations for every scheme and module, including empty schemes and rank zero.
The original statement is verified as a private Lean theorem without adding hypotheses.

There are no current Lean importers of the quarantined path. The archived parent is
preserved and still cites this node; this delivery does not treat its absence as pruning.
Its future restoration may use the reexported equality to translate the canonical result.
Searches through msearch (LeanFinder, Loogle, grep) found no Mathlib theorem matching the
derived diagonal formula. Local rg found the exact upstream implementation and the
existing exterior-sheaf equality, which are used here.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
