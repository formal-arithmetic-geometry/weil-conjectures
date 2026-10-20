## What changed

Restored Sheaf.Paper.ModuleCupGlobalTensorPullback from its exact quarantine
archive and replaced its empty Sheaf.Algebra.Homology.KFlatPullback public
import with the defining upstream module
WeilConjectures.Algebra.Homology.KFlatPullback. This repairs the recorded public
visibility error for CochainComplex.tensorPullbackRingMap. All remaining source
text, declarations, signatures, definition bodies, and proofs are unchanged.

The existing proof obtains ordinary pullback and its normalized counit from
exists_globalTensorPullback_underived_data, obtains the derived comparison from
exists_globalTensorPullback_derived_data, and packages their conjunction. Both
DAG proof dependencies and their Lean signatures were checked. No route or node
change is required. The node's Lean attachment is preserved.

Single-file lcompile succeeded without warnings, reporting 25.9 seconds.
A separate public-import consumer compiled in 1.5 seconds and checked visibility
of tensorPullbackRingMap, moduleCup_globalTensorDiagram, and the global
comparison theorem (the dependency recompile took 26.8 seconds). Its
#print axioms checks found exactly propext, Classical.choice, and Quot.sound
for both declarations; no sorryAx. This temporary check file is not delivered. The change
record is coord/changes/module-cup-global-tensor-pullback-import.md.

## Proved and sorry left

This is a zero-hole rework repair. The module had zero sorry bodies and still
has zero. No holes closed, no holes added, and none split off.
The existing completed proof of
AlgebraicGeometry.Scheme.Modules.globalRingedSpace_derivedTensor_pullback_comparison
is preserved. The definition
AlgebraicGeometry.Scheme.Modules.moduleCup_globalTensorDiagram is unchanged.

## No longer needed

Removed the import Sheaf.Algebra.Homology.KFlatPullback, now an empty withdrawn
compatibility module. Its actual upstream replacement is explicitly public
because the statement uses its declarations. No mathematical nodes or modules
are pruned, and both proof dependencies remain necessary. No declaration in the
adopted source tree is changed or removed.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantine repair rather than an open proof: the archived module
already has zero sorry bodies. Its former public import did not expose the
upstream ring-map definition after the Sheaf module was withdrawn. This is the
exact failure listed in coord/rework.tsv, repaired without changing mathematics.
LeanFinder returned scheme pullback results rather than a replacement for the
existing global comparison proof; Loogle does not index the project ring-map
name. Local source search locates its definition in the upstream KFlatPullback
module. No new lemma or alternative proof route is necessary.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
