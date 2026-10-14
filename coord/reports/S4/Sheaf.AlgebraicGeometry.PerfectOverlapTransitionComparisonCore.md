## What changed
The core theorem now performs a genuine two-step reduction: it obtains an eventual
stage overlap isomorphism from `perfect_overlap_transition_comparison_core_stage`,
then applies fixed-stage coherence to that supplied isomorphism and packages the
result. The coherence theorem now takes the stage isomorphism as an explicit input,
so it is a strictly smaller fixed-stage transport statement rather than a restatement
of the target. The unused reflexive stage-existence helper was removed.

## Proved and sorry left
Closed: the reduction proof of `perfect_overlap_transition_comparison_core`.
Sorry left: `perfect_overlap_transition_comparison_core_stage` (node
`lem-pc-perfect-overlap-transition-comparison-core-stage`) and
`perfect_overlap_transition_comparison_core_coherence` (node
`lem-pc-perfect-overlap-transition-comparison-core-coherence`). No new holes were
added beyond these two named split-off statements.

## No longer needed
The temporary theorem `perfect_overlap_transition_comparison_core_stage_exists` was
removed because the target already receives `hstage` and the theorem was unused.
No imports were removed; all remaining imports are needed by public signatures or
by the split-off theorem statements.

## Where the brief, the DAG or earlier work was wrong
The earlier proof introduced coherence without passing the stage overlap isomorphism
produced by the stage theorem. That made the supposed reduction independent of the
preceding construction and too close to a restatement of the target. The interface
was repaired by making the fixed-stage theorem consume the supplied isomorphism and
by explicitly packaging it in the target proof.

## Earlier second reading (a previous round; superseded)
The stage theorem quantifies over the directed preorder, colimit cocone, geometric
map, finiteness hypotheses, stage-existence hypothesis, compact cover, perfect local
objects, and comparison object exactly as in the target. Its conclusion supplies
`k`, `hjk`, and an overlap isomorphism between the two exact overlap restrictions;
the proof description explicitly restricts to the compact overlap, descends both a
morphism and inverse, enlarges the stage for the identity equations, and transports
through canonical pullback and restriction comparisons.

The coherence theorem repeats the fixed-stage data and quantifies over every supplied
`e₀ : SU.obj A' ≅ SV.obj B'`. Its existential output contains only the comparison
diagram and the two local identifications. The displayed equality uses
`d.toDiagram.HW.map e₀.hom` directly, so the supplied overlap isomorphism is the
one used by the construction and no unused or freshly chosen overlap variable is
present. The hypotheses, lets, and category interfaces remain unchanged.

The target proof first applies the stage theorem to obtain `k`, `hjk`, and `e`, then
applies coherence at precisely that stage with `e₀ := e`, and finally packages
`d`, `e`, `θU`, `θV`, and the returned equality into the target existential. Thus
both new statements are strict substeps of the target proof and the DAG route is
acyclic: the stage and coherence nodes depend on definitions and lower comparison
lemmas, while the existing core node depends on those two nodes. In particular,
neither new node cites the existing core item node. No declaration signature or
visibility was changed; only the coherence output interface was corrected to use
its supplied input, with the corresponding target packaging adaptation.

## New nodes
`lem-pc-perfect-overlap-transition-comparison-core-stage` records eventual overlap
transition existence and is stated in the item's module. `lem-pc-perfect-overlap-transition-comparison-core-coherence` records fixed-stage coherent transport with a
supplied overlap isomorphism and is stated in the item's module. No change records
were needed.

Change record: `coord/changes/PerfectOverlapTransitionComparisonCore-proof-options.md`.

## Second reading by S4

1. I compared the delivered module with the repository version. The existing target declaration is byte for byte unchanged; the added declarations are split-off proof statements, and the only proof-only option change is `set_option linter.unusedVariables false`.

2. I compiled the module with `lcompile.py`; it succeeds. The only remaining `sorry`s are the two named split-off theorems `perfect_overlap_transition_comparison_core_stage` and `perfect_overlap_transition_comparison_core_coherence`; no definitions contain `sorry`, and no forbidden declarations were added.

3. The stage and coherence statements are true and strictly smaller than the target: the stage theorem supplies only an eventual overlap isomorphism, while coherence consumes a supplied fixed-stage isomorphism and constructs the comparison data. Neither restates the target, and both have matching DAG nodes and source/docstring proofs.

4. The target proof follows the shortest available reduction through those two split-off statements, passing the stage-produced isomorphism into coherence. Its proof dependencies and node route agree with the Lean code; no unused imports or old helper theorem remain.

5. The unit route is preserved: the existing core node now depends on the stage and coherence nodes, and both new nodes remain below the unit-level comparison construction. No statement or definition change record is needed.

Changed during second reading: added this review section only; no Lean declarations, node statements, or imports were altered.
