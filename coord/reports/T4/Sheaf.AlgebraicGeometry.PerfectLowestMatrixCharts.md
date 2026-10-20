## What changed

Restored the quarantined module Sheaf.AlgebraicGeometry.PerfectLowestMatrixCharts
from its rework archive. Redirected its proof-only DerivedPullbackComposition
import from the withdrawn Sheaf wrapper to the canonical WeilConjectures module.
Removed the unused proof-only FlatComplexDerivedPullback import. The declaration
AlgebraicGeometry.Scheme.exists_perfectLowestMatrixCharts, its full signature,
public imports, and complete proof are otherwise unchanged.

The node lem-sc-perfect-lowest-matrix-charts keeps its Lean attachment and all
five proof dependencies. The existing three-step argument still obtains a residue
model, restricts it inside the prescribed open, applies the affine matrix-locus
lemma, and transports fixed-rank local freeness through derived composition and
homology. No unit route changes.

Validation: lcompile.py --all compiled the unchanged current source of
AffineFreeLowestMatrixLocus and then the restored item (8 seconds), without
warnings. The dependency copy is byte-identical to the shared repository and is
included only for compilation against the current source; it contributes no diff.
The published dependency artifact still imported the old Sheaf derived pullback,
which caused the original duplicate-declaration diagnostic when compiling the
item alone. No dependency declaration was recreated or changed.

Change record: coord/changes/T4-perfect-lowest-matrix-charts-restore.md.

## Proved and sorry left

This is a zero-hole rework repair. The archived declaration
AlgebraicGeometry.Scheme.exists_perfectLowestMatrixCharts already had a complete
proof; it is restored with that proof and the corrected import. Holes closed: 0
of 0. Holes added: 0. No sorry remains in the item or the unchanged dependency
source submitted for compilation. No theorem was split off. Existing transitive
proof holes are not claimed as closed.

## No longer needed

Removed the direct import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback:
the item uses the affine matrix-locus theorem rather than a separate flat-complex
comparison. The flat-complex mathematics remains below that dependency.
Replaced Sheaf.AlgebraicGeometry.DerivedPullbackComposition by
WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition, retaining the same
node lem-pc-ringed-spaces-derived-pullback-composition. No mathematical dependency
or module is withdrawn or globally pruned.

## Where the brief, the DAG or earlier work was wrong

The assigned file was absent from lean because of the upstream-sync quarantine,
not because its theorem was unused. Restored its archived proof rather than
withdrawing it. Its quarantined consumer PerfectLowestMatrixClosedLocus still
calls exists_perfectLowestMatrixCharts with exactly the retained signature; its
DAG also retains this dependency. No consumer adaptation is required.

Read the current signatures for the residue model, restriction, affine matrix
locus, derived composition, and fixed-rank invariance. They supply every input
used in the unchanged proof. The rank bound is at U.ι x throughout; eK.symm and
the composition isomorphism identify the correct pullback; eH and eH.symm give
the two directions of rank transport. There is no new edge-case assumption:
empty U has no point x; zero ranks and reversed amplitude intervals pass to the
same existing model and affine-locus lemmas.

LeanFinder returned only underived Mathlib pullback composition results. Library
search found the canonical source exists_derivedPullbackComposition, with the
same existential composition field used by the proof. No shorter replacement
for the local chart argument was found or needed. The node and statement remain
unchanged. No source-library declaration was edited.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
