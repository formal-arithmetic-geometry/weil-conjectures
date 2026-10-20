## What changed

Retired the duplicate Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent,
as assigned by coord/retire-items.tsv. Its upstream twin already proves
isQuasicoherent_exteriorSheaf_of_isAffine for Scheme.Modules.exteriorPower.
The sole direct consumer, SelfTorConormalWedgeChartFromSections, now privately
imports that upstream module. Two proved private helpers identify the old exterior
presheaf with the canonical upstream presheaf using uniqueness on pure wedges,
then identify their sheafifications. Rewriting this equality allows the existing
consumer proof to use the upstream theorem with its public signature unchanged.

Updated new-q1-exterior-sheaf-quasicoherent to attach to the upstream declaration,
with its exact signature and existing:true. Updated that node's proof description
and the consumer node's exterior quasi-coherence step. Dependency sets and unit
route are preserved. Change record:
coord/changes/retire-exterior-sheaf-quasicoherent.md.

## Proved and sorry left

The item had zero sorries before retirement: 0 of 0 holes closed, 0 added,
0 split off, 0 left. The adapted consumer has zero sorries.
The upstream isQuasicoherent_exteriorSheaf_of_isAffine remains fully proved.
The existing exists_selfTor_conormal_wedge_chart_from_sections proof is complete.
The two new private helpers exteriorSheafPresheaf_eq_upstream and
exteriorSheaf_eq_upstream are fully proved. No new public declaration is added.

The adapted consumer compiles through lcompile.py in 12.9 seconds. The next
importer, SelfTorConormalWedgeChart, compiles against the adapted consumer in 2.9 seconds.
The consumer also compiles in that dependency-ordered set in 12.8 seconds.
Its public signature and public imports compare verbatim equal to the originals.
The overlaid import closure excludes the retired module and adds no twin pair.
The delivery tool runs its axiom probe and preflight before pushing.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent.
Removed its private import from SelfTorConormalWedgeChartFromSections; replaced
it with WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafQuasicoherent.
The duplicate module's separate localization and sheafification proof is removed.
Its mathematical node is retained and points to the upstream proof. The node's
existing localization, affine-unit, exterior-power and quasi-coherence-criterion
dependencies remain needed by that upstream proof; no such node is pruned.
No source-library declarations or modules are removed or changed.

## Where the brief, the DAG or earlier work was wrong

This is the listed retirement task, although the generic brief describes proving
holes. The item already has zero holes. The local and upstream theorem names agree
but their conclusions mention exteriorSheaf and exteriorPower respectively, so
an import replacement alone would not preserve the consumer proof. The proved
presheaf and sheafification equalities supply the required compatibility.
The consumer node's old description called this an unfinished prerequisite;
it is now an existing proved upstream result, and that stale sentence is removed.

Searches made through msearch.py: LeanFinder for exterior quasi-coherence, Loogle
for IsQuasicoherent, and grep for isQuasicoherent_exteriorSheaf_of_isAffine.
Mathlib search supplied general quasi-coherence and exterior-power constructions;
direct rg over the source library found the exact existing upstream theorem.
There are no new nodes or new mathematical proof obligations.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
