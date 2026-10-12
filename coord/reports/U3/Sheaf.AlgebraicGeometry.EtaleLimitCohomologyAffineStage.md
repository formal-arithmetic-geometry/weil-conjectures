## What changed

Replaced the sorry in `AlgebraicGeometry.Etale.etale_limit_cohomology_affine_stage` by a complete Lean reduction. The proof constructs the directed upper tail, proves its inclusion final, transports affineness from the selected stage, proves every tail stage affine, preserves the scheme limit and coefficient colimit, applies the supplied `haffine`, and reflects the resulting cohomology colimit. The existing theorem signature is unchanged.

Added `Sheaf.AlgebraicGeometry.EtaleReindexTransitionCoherence` and `Sheaf.AlgebraicGeometry.EtaleReindexComparisonCoherence`, imported only for the proof. Their seven data constructors are real restrictions with explicit reflexive equality transports. There is no data chosen from an unproved existence theorem. The two coherence theorems are proved by direct specialization of the supplied equations under an arbitrary preorder functor; neither assumes affine continuity or asserts a colimit property. The parent DAG proof and dependencies now name them.

The original higher-order hypothesis names several proof binders which do not occur in its conclusion. Its signature is preserved verbatim, with the unused-variable linter scoped off for this declaration to avoid warnings about those nested binders.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.etale_limit_cohomology_affine_stage` (node `lem-weil-pbc-etale-limit-cohomology-affine-stage`) and repaired the two returned coherence holes: `AlgebraicGeometry.Etale.reindex_etale_transition_coherence` and `AlgebraicGeometry.Etale.reindex_etale_comparison_coherence`. All three declarations now compile with complete proof bodies. No sorry remains in this item or its two added modules; all seven reindexing data constructors are real definitions.

## No longer needed

No original dependency node or module is pruned: the cofinality Mathlib leaf and scheme conventions remain used. The direct proof import of `Mathlib.AlgebraicGeometry.Morphisms.Affine` was unnecessary because the statements already expose its API transitively. A redundant direct import of `EtaleReindexTransitionCoherence` was removed: `EtaleReindexComparisonCoherence` publicly imports it because its statements use the concrete coefficient restrictions. The transition lemma itself remains needed.

Discarded the earlier sandbox-only `EtaleLimitCohomologyAffineStageCore` module and the sandbox-only tail-reduction node/theorem. Neither ever landed, and neither is part of this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's tail-reduction theorem repeated the entire original statement and was not a reduction. Its claim that no usable finality declaration existed was incorrect: the DAG dependency is a Mathlib leaf, with `Functor.Final.isColimitWhiskerEquiv` and `Functor.Initial.isLimitWhiskerEquiv`; `Monotone.final_functor_iff` proves finality of the actual tail.

The original DAG treats all dependent coefficient restriction equations as elementary glue. The returned delivery left the two coherence definitions as timeout-driven holes. This repair replaces both holes with checked proofs by direct specialization of the supplied equations, while retaining the actual constructions, the tail geometry, the affine-continuity application and the colimit transfer in the parent proof. The two new statements were checked on empty index categories, arbitrary functors, empty schemes and degree zero: none of these cases requires extra hypotheses.

The source `.tex` file is not present in this clone; Tag 09YQ was read on the official Stacks page. LeanSearch returned Internal Server Error for both new nodes, recorded as unavailable; LeanFinder, Loogle, Mathlib grep and repository grep found no existing exact interface. Blueprint searches found no node for either restriction coherence statement. The blueprint ancestor command returned None for the new parent; the new nodes retain the parent's recorded blueprint ancestor and route.

## New nodes

`lem-weil-pbc-etale-reindex-transition-coherence` states only preservation of coefficient identity and composition equations by the concrete restrictions; it is independent of affine geometry and continuity. Its module contains the real coefficient and transition constructors. Source: the coefficient restriction step of the parent's Tag 09YQ reduction. It applies to arbitrary preorder functors, including empty domains.

`lem-weil-pbc-etale-reindex-comparison-coherence` states only preservation of the three supplied comparison equations by concrete whiskering and restricted identifications. Its module constructs the restricted sheaf diagram, cocone, pullback isomorphisms, cohomology isomorphisms and vertex isomorphism. It assumes neither transition coherence nor any limit or colimit property. Source: the comparison restriction step of the same reduction. No existing interface or target statement is changed, and no forced adaptation or change record is needed.

## Earlier second reading (a previous round; superseded)

1. I compared the delivered affine-stage module with the repository version. The target theorem signature is unchanged byte for byte; only proof imports, linter scope, and proof text changed. Verdict: pass.
2. I compiled all delivered modules with `lcompile.py`; the item and its import closure compile without errors, and no `sorry` remains in the repaired modules. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. The two repaired statements are strict reductions of the parent proof: transition identity/composition preservation and comparison-equation restriction. Their constructors are explicit equality transports, and their proofs directly specialize the supplied equations. Repository and Mathlib searches found no existing equivalent declarations. Verdict: pass.
4. The proof uses the final tail functor, its initial opposite, the affine continuity hypothesis, and final colimit reflection. The added imports are proof-only where applicable, and no original dependency node is pruned. Verdict: pass.
5. The DAG proof, proof dependencies, and proof origins match the Lean route; the unit route remains realized through the parent node. Verdict: pass.

I restored one extra space before the parent theorem's `:=` so the existing signature text is byte for byte identical to the repository. No mathematical declarations or DAG records required repair. I checked the two new node signatures verbatim against Lean, their proof-dependency unions, and that the parent changes only `proof`, `proof_deps`, and `proof_origin`. The unit's realized nodes are untouched; this is a reduction below the unit level, retaining the parent continuity route.

The scratch `#print axioms` checks for the repaired declarations show only `propext`, `Classical.choice`, and `Quot.sound`; all seven data constructors have only the three standard axioms. I independently searched with the alternative phrases “precomposing a coherent family of pullback sheaves” (LeanFinder), “whisker”, “map” (Loogle), and `upperStarComp|upperStarId` (Mathlib grep), plus repository restriction/whiskering searches. No result provides these exact dependent equations. For an empty domain the conclusions are vacuous; for a singleton the transition statement is its original identity law; for identity reindexing every equation is the supplied equation. Arbitrary reindexing selects original maps, with proof irrelevance identifying preorder morphisms and equality proofs. Empty schemes and degree zero change none of this argument.

I repaired both coherence theorems by applying `hidentity`/`hcomposition` and `hG`/`hH`/`hB` at the selected indices. The repaired modules and the full sandbox import closure compile successfully within the existing compiler limits. The final delivery contains no timeout-created holes.

I reread the official [Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ); it states continuity for the directed scheme system and abelian coefficient system. The tail and coherence lemmas are agent-written reductions, as their source records explicitly say, rather than separate quoted statements of that tag.

## Second reading by U3

1. Compared the delivered parent module with the repository version. The target theorem signature is unchanged byte for byte; only proof imports, linter scope, and proof text changed. Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py`; they compile without errors. There are no `sorry`, forbidden declarations, or hollow definitions in the delivered files. Verdict: pass.
3. Checked the two new coherence statements and their explicit restriction constructors. They are true specializations of the supplied equations, strictly smaller than the parent target, and repository/Mathlib searches found no existing equivalent declarations. Verdict: pass.
4. Checked imports and pruning. Proof-only imports are plain imports; the final-tail and affine continuity route is retained, and no original dependency node is pruned. Verdict: pass.
5. Checked the parent and new DAG nodes against the Lean declarations, proof dependencies, and origins; the unit route remains realized. Verdict: pass.

Changed only this report section after the prior review: it records the required second-reading verdicts explicitly.
