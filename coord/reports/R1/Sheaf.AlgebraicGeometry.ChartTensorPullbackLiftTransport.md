## What changed

Replaced the first worker's `ChartTensorPullbackLiftTransportCore` restatement with a
real reduction in `Sheaf.AlgebraicGeometry.ChartTensorPullbackLiftTransport`. The proof
unfolds the ordinary recovery equation and extracts its original chart lift and comparison,
constructs the direct restriction comparison, and uses one-object coherence at F and G.
It performs the remaining transport by naturality and inverse cancellation. An elementary
cancellation calculation is proved in a private helper in the same module, with abstract
functors so that simplification does not unfold the scheme-chart constructions.
No existing signature, definition, docstring or public import changed. The new coherence
module is imported only for the proof.

`Sheaf.AlgebraicGeometry.ChartTensorPullbackComparisonCoherence` isolates the comparison
path identity for one module, with no second module, morphism, chart map or recovery
hypothesis. Its named theorem remains open and has a natural-language proof and node.
The target node's proof and dependencies now describe the actual reduction. The untouched
`ChartOrdinaryMapRecovery.lean` source is retained in the sandbox solely because the
shared compiled library lacks its artifact; it is byte-identical to the repository and
is not a changed delivery module.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.chart_tensor_pullback_lift_transport`
(node `lem-pc-chart-tensor-pullback-lift-transport`), by a genuine transport calculation
conditional on the smaller comparison-path identity.

Hole added and left: `AlgebraicGeometry.chart_tensor_pullback_comparison_coherence`
(node `lem-pc-chart-tensor-pullback-comparison-coherence`). Its proof is exactly
`by sorry`; there are no holes in definitions or in the item's partial proof.

This is a **decomposition**, not a fully proved import closure: one upper hole closed,
one strictly smaller lower hole added, net zero. The original core restatement and its
node were removed before delivery; they are not extra holes in the final set.

## No longer needed

No repository import or module is pruned. Every original public import occurs in the
unchanged signature. The rejected core module was never part of the repository and
is removed from this delivery.

The original direct proof dependencies `lem-pc-module-pullback-adjunction` and
`lem-sc-left-adjoint-composition-iso-associativity` are no longer direct steps of the
item's proof: they now belong to the new comparison-coherence node's proof plan.
They remain needed transitively, so neither is claimed as pruned. All other original
proof dependencies remain direct dependencies, and the comparison-coherence node is
added. No unit realization is removed or changed.

## Where the brief, the DAG or earlier work was wrong

The first worker's core statement was definitionally the original item after unfolding
its lets. Introducing s and its hypothesis before applying that restatement did not
make it a strictly smaller step. That delivery was therefore not acceptable, regardless
of whether a syntactic restatement detector happened to accept it. The second reader
replaced it with just the one-object comparison identity from the original coherence
step, and supplied the complete remaining morphism-transport calculation.

The shared library is missing `ChartOrdinaryMapRecovery.olean`. The sandbox already
contained the identical dependency source; it compiles with the permitted local compiler.
No library source or compiler tool was modified. LeanSearch returned Internal Server
Error; the failed search and successful LeanFinder, Loogle and grep searches are recorded
in searches.jsonl.

## New nodes

`lem-pc-chart-tensor-pullback-comparison-coherence`, in
`dag/nodes/sec-picard-framework/`, states the equality of the two explicit comparison
paths on a single module. Its source is Stacks Tags 0095 and 0096 for the pullback
adjunction, with Mathlib's ordinary pseudofunctor associativity and adjunction mate
associativity for the comparison calculation, expanded by R1. This isolates only the
coherence part of the old plan. There are no change records because no existing
statement or definition changed.

## Second reading by R1

1. Compared every sandbox source with its repository version. The item's existing
   theorem signature is byte-for-byte unchanged; its original docstring and all public
   imports are unchanged. ChartOrdinaryMapRecovery is byte-identical. The only new
   declaration is the one-object comparison identity. No definition or statement was
   altered to ease the proof. Verdict: pass after removing the core restatement.
2. Checked the source for sorry, axioms and prohibited declarations. Only the named
   comparison-coherence theorem contains sorry; all data (including v, d, b and c) are
   explicit constructions. Compilation and axiom audit results are recorded below.
   Verdict: conditional transport proof, with exactly the reported coherence hole.
3. Read the smaller statement and its full docstring argument. It is the canonical
   comparison-path identity, without any morphism-transport or recovery assertion.
   The two projection equations supply exactly the required diagram commutativity.
   Identity arrows use the same selected adjunctions on both paths, so their comparison
   factors cancel; zero modules and empty schemes have unique zero comparison maps;
   an empty cover has no index a and is vacuous. No nonzero or nonempty assumptions are
   hidden. Independent searches under restriction/composition terminology found only
   the general Mathlib ingredients, not this mixed tensor/ordinary chart identity.
   Verdict: true, strictly smaller part of the original argument, still unproved in Lean.
4. Checked the top-down reduction and imports. The morphism argument uses the supplied
   recovery equation and naturality explicitly; it is not an application of a renamed
   recovery theorem. The smaller hole is the original canonical coherence substep.
   Both ordinary pseudofunctor and mate associativity are available as ingredients,
   but neither directly supplies the mixed comparison identity, so it is retained.
   The unit sk-thm-picard-semicon has empty realized statement/step lists in the baseline;
   no realized node or chapter/unit route is bypassed. No original module is pruned.
   Verdict: pass; decomposition with net zero, as reported above.
5. Checked the target and new node records against the Lean. The target's original
   statement and Lean signature record are preserved. Its updated proof names the
   actual recovery, comparison and cancellation steps. The new node has its source,
   complete proof plan, exact Lean signature, dependency union, search records, origin,
   blueprint parent, chapter, unit and creation fields. Verdict: pass.

Second-reading changes: removed the rejected core theorem/module/node; introduced the
strictly smaller one-object comparison-coherence theorem/module/node; wrote the genuine
transport reduction and private elementary cancellation proof; updated the target node;
corrected the progress count and pruning report.

The coherence theorem accepts any chart refinement with the two projection equations,
and supplied d and b isomorphisms with equalities requiring precisely the canonical
ordinary comparison constructions. Its statement does not reconstruct the canonical lift.
The target supplies its exact d and b with reflexive canonicality equalities. In the target proof, the lift and
d are extracted directly from the ordinary recovery hypothesis, avoiding duplicate data
constructions. The zero-module edge case was independently proved in a scratch copy
without using the coherence hole; its axiom audit showed only propext, Classical.choice
and Quot.sound. No scratch theorem is delivered.

Final local compilation: all three sandbox source modules compile without warnings
(recovery dependency 2.3 s, new coherence module 2.8 s, repaired item 19.2 s). The source
comparison confirms the original target signature byte-for-byte and confirms recovery
is unchanged. No target or definition semantic review is reopened.

Final axiom audit: chart_tensor_pullback_lift_transport and the new coherence theorem
use exactly propext, Classical.choice, Quot.sound and sorryAx. The proved private
comparison_transport helper uses only propext, Classical.choice and Quot.sound. The
independently proved zero-module version of the final coherence signature also uses
only those three axioms. No other axiom or prohibited declaration was found.

Delivery-gate repair: the first dry run required a change record for top-level local
reducibility attributes. They were unnecessary for the final explicit-comparison proof
and were removed. The item compiles without them, without warnings, in 24.6 s. There
are no added top-level attribute commands, public imports, or other visibility changes
in the existing module, so no interface change record is needed.
