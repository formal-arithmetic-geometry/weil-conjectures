## What changed

Withdrew Sheaf.AlgebraicGeometry.CompatibleImmersionGluing, the zero-hole retirement
item. Redirected lem-sc-compatible-immersion-gluing to the proved theorem of the same
name in WeilConjectures.AlgebraicGeometry.CompatibleImmersionGluing. The upstream
version omits the unused hU hypothesis, so it directly proves the old statement.
The adopted source library is unchanged.

Change record: coord/changes/compatible-immersion-gluing-retirement.md.

## Proved and sorry left

Initial holes: 0. Holes closed: 0. Holes added: 0. Holes remaining: 0.
No decomposition and no split-off theorems.

AlgebraicGeometry.Scheme.exists_gluedCompatibleImmersionCharts remains completely
proved upstream, together with its private compatibleImmersion_openOverlap and
exists_gluedMonoOpenAtlas helpers. A scratch specialization checks the old signature
against the upstream theorem. Both it and the retained theorem have exactly the
permitted axioms propext, Classical.choice and Quot.sound. The original Sheaf module
compiled in 2.1 s; the signature specialization in 2.0 s, and the unchanged upstream
consumer LocalImmersionLocus in 3.0 s. No delivered Lean proof remains to compile.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.CompatibleImmersionGluing. No tracked Lean module
imports it in the current repository: tools/downstream.py reports 0 downstream
modules, and its declaration-use scan lists only the retiring module itself.
The old public Mathlib immersion import and
private Mathlib gluing import disappear with this unused copy. The retained upstream
proof still uses the Mathlib scheme-gluing and morphism-gluing results represented by
lem-weil-pbc-glue-schemes and lem-weil-pbc-scheme-morphism-gluing; neither DAG dependency
is pruned. The node itself stays, attached to the upstream theorem. No other module
or node is declared unnecessary.

## Where the brief, the DAG or earlier work was wrong

This is a retirement item, as coord/queue.tsv records, rather than an unfinished
proof: the supplied module has no sorry. The historical kept-twins reason says the
upstream API differs; reading the signatures shows that the only public difference
is the omitted unused hU hypothesis. The former consumer has already migrated to
upstream in the current tree, so no consumer edit is necessary. Empty bases, empty
patches, and arbitrary non-covering families are included by the stronger retained
theorem; no extra existence or choice assumption is introduced.

Searches: msearch.py leanfinder found the Mathlib GlueData interface; loogle did not
index the project-specific theorem, and its grep service returned no hits. Direct rg
and reading both local library modules found the upstream proof and confirmed the
absence of Sheaf importers. No new nodes.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
