## What changed

Restored Sheaf.Paper.PbcUniformReductionCriterion from the exact archive named by
coord/rework.tsv (cluster restore at 5f7b33eac, 2026-10-20). Preserved both public
signatures, the coefficient constructions, imports, and the node attachment and
proof dependencies. The reverse implication uses the canonical reduction tower,
normalizedConstructibleTower_local_effectivity, exact coefficient realization, and
bounded-below site comparison to construct compatible origins. The forward implication
uses pbcUniformLocalModelCohomology.

Shortened the proved private etaleComparison_reflects_isGE helper using the existing
Functor.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj lemma.
It replaces the repeated homology comparison and faithful zero-morphism argument by
that already proved API. This does not change the proof route.

The restored archive first failed to compile because the published build lacked
PbcUniformLocalModelCohomology. A temporary byte-identical copy of its current source
was compiled alongside the item, successfully (14.1 and 7.5 seconds). The revised item
then compiled successfully in 11.0 seconds. That dependency copy is scratch material
only, not a delivered adaptation. The delivery tool runs the final compile and probes.

Change record: coord/changes/B2-uniform-reduction-criterion-restoration.md.

## Proved and sorry left

Both AlgebraicGeometry.Scheme.pbcUniformReductionCriterion_backward and
AlgebraicGeometry.Scheme.pbcUniformReductionCriterion are fully proved from the stated
project APIs. The archive already had zero direct holes; this is a quarantined-module
restoration, not a claim of new hole closure. Holes closed: 0. Holes added: 0.
Sorries left in the delivered module: none. Split-off statements: none.
Some imported project APIs remain unproved in their own modules; none is restated here.

The reflection helper now applies the existing proved faithful-exact-functor API.
The reverse construction handles an empty input cohomological interval using [min a b,b].
Constructibility transport preserves the given stratification and all finite models.
The realization comparison is chosen from a uniquely normalized existence theorem,
pbcAssociatedRestriction_exists, not from an arbitrary unproved existence assertion.
All origin choices occur only inside a proof of existential witness predicates.

## No longer needed

None. No imports, nodes, modules, declarations, or unit steps are pruned. In particular,
LevelwiseAdicTruncations remains necessary for its canonical pbcReductionAdicTower and
its coherence fields, even though this proof does not use its truncation assertions.
The node lem-weil-pbc-uniform-reduction-criterion and its dependencies stay attached.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, rather than present under lean/. Its archived proof
already has no sorry. The recorded reason is a cluster-restore reversion, with no
specific mathematical defect recorded. Restoring its declarations repairs their
absence; no definition or theorem statement is weakened or replaced. The current
archive compiles against current dependency sources.

The two direct consumers are themselves quarantined:
Sheaf.Paper.PbcConstructibleReductionCriterion applies both restored public theorems,
and Sheaf.Paper.PbcUniformCompleteTriangulated applies the restored equivalence.
Their applications retain exactly the same signatures. The corresponding DAG parents
still need this node, and the unit route is preserved. No consumer adaptation, new
node, source-library edit, or public-interface change is needed.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
