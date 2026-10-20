## What changed

Restored the quarantined assigned module as a public compatibility import of
`WeilConjectures.AlgebraicGeometry.DerivedPullbackSingleCohomology`, which already
provides the same public theorem with a complete proof. Reattached
`lem-pc-derived-pullback-single-cohomology` to that source declaration. The source
explicitly qualifies `AlgebraicGeometry.derivedPullback`, distinguishing the original
model functor from `Scheme.Modules.derivedPullback`. No source file is changed.

The node's statement, proof steps, proof dependencies and unit route are retained.
The sole DAG parent `lem-pc-flat-rf-open` still cites this node. Its live Lean consumer
`PerfectLocusOfRank` already imports the adopted source theorem, so no consumer edit
or parent dependency removal is needed. The quarantine archive is preserved and
`deleted.txt` is not used.

Change record: `coord/changes/A7-derived-pullback-single-cohomology-upstream.md`.

## Proved and sorry left

Zero initial textual holes; zero holes closed; zero holes added; zero split off;
zero holes remain in the restored module. This delivery repairs an upstream overlap,
not a new mathematical proof. The existing theorem
`AlgebraicGeometry.Scheme.Modules.nonempty_homology_derivedPullback_iso_of_locally_single`
(node `lem-pc-derived-pullback-single-cohomology`) is fully proved in the adopted source.
A fresh single-file compile of its unchanged proof reports only `propext`,
`Classical.choice`, and `Quot.sound` under `#print axioms`. Its pre-existing long-line
lint warning at line 153 is outside this delivery's edits.

## No longer needed

The duplicate Sheaf implementation and its private flat-single helper are no longer
needed because the adopted source contains both complete proofs. Its archived import
list is replaced by the single source-module compatibility import. In particular,
`Sheaf.AlgebraicGeometry.DerivedPullback`,
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`, and
`Sheaf.AlgebraicGeometry.DerivedSingleOpenLocus` are no longer used here. The direct
imports of `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex`,
`WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback`,
`WeilConjectures.CategoryTheory.Abelian.Flat.Basic`, and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed` are supplied by the
source module. Their mathematical dependencies remain necessary to its proof.
No DAG node or mathematical proof dependency is pruned. The assigned module remains
as a compatibility path, so no whole module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The rework row correctly records an import collision, but the DAG attachment still
points to the quarantined Sheaf duplicate after the corresponding complete theorem
was adopted upstream. Recreating the old declaration would create another collision.
The source statement agrees hypothesis by hypothesis with the node: arbitrary schemes
and morphism, the same derived-category instance family, connectivity, local finite
freeness in one natural degree with varying rank, and the same cohomology isomorphism.
The empty image, zero rank, empty scheme and all natural degrees remain covered.

Searches through msearch (LeanFinder, Loogle, grep) and direct source search were run.
Loogle supplies the single/homology comparison; direct source search supplies the exact
complete theorem. No new lemma, axiom, definition or target statement is introduced.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
