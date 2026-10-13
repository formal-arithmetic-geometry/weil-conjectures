## What changed
Replaced the sorry in `AlgebraicGeometry.Etale.etale_limit_affine_stage_tail_colimit`
with a proof restricting the system to the directed upper tail. The proof constructs
its nonempty and directed instances and proves its inclusion final, preserves the
scheme limit and coefficient colimit by whiskering, proves every tail scheme affine,
and applies `etale_limit_cohomology_affine_comparison` to the restricted data.

Added the proof-only import `Sheaf.AlgebraicGeometry.EtaleLimitReindexTransitionCoherence`.
No existing signature or public import changed. The second reader removed the
three redundant Mathlib imports for finality, whiskering and affine morphisms;
they are already publicly imported through TopologicalInvariance. The new theorem
isolates only the two coefficient
identity/composition equations, with no geometric, limit, colimit, or cohomological
hypotheses or conclusion. The original node records this remaining dependency.

## Proved and sorry left
Closed the original hole in `AlgebraicGeometry.Etale.etale_limit_affine_stage_tail_colimit`
(node `lem-weil-pbc-etale-limit-affine-stage-tail-colimit`). There are no sorries in the
item's module.

Added one hole: `AlgebraicGeometry.Etale.etale_limit_reindex_transition_coherence`
(node `lem-weil-pbc-etale-limit-reindex-transition-coherence`). It states only that
reindexing a coherent inverse-image transition system preserves identity and
composition. This is a decomposition: one upper hole closed, one strictly smaller
lower hole added; net zero holes. No data is chosen from an unproved theorem.

## No longer needed
Removed the redundant direct imports `Mathlib.CategoryTheory.Filtered.Final`,
`Mathlib.CategoryTheory.Limits.Final` and `Mathlib.AlgebraicGeometry.Morphisms.Affine`
added by the first worker. These modules remain in the transitive public import
closure, so no library module is pruned. Both original imports and all original
proof dependencies remain needed. The finality leaf is a Mathlib match used by
`Functor.final_of_exists_of_isFiltered` and the whiskering equivalences.
The unit's realized statements and steps are preserved. No geometric or cohomological
module is bypassed, and no pruning is claimed.

## Where the brief, the DAG or earlier work was wrong
The mathematical route in the DAG fits. Its assertion that reindexed coherence laws
follow by functoriality hides dependent Lean transport through `eqToIso` and
`upperStarComp`. Direct elaboration of those equalities repeatedly exceeded the
single-file limit. That step is now isolated with a complete proof in words, instead
of leaving an anonymous sorry in the target. Inlining restricted data in the affine
comparison application and unfolding the whiskered comparison leg avoids slow
comparisons of dependent local aliases. The complete item compiled in 29.1 seconds.

## New nodes
`lem-weil-pbc-etale-limit-reindex-transition-coherence`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-limit-reindex-transition-coherence.json`,
is the general reindexing of the two coefficient coherence equations, following the
cofinal-tail restriction of Stacks Tag 09YQ (theorem-colimit). Its source, complete
proof in words, exact Lean statement, and three actual searches are recorded. It is
strictly simpler than the target: no directedness, affine stage, limit cone, coefficient
colimit, cohomology, or comparison cocone occurs. Empty and singleton preorders are
valid edge cases. Blueprint search for reindex transition coherence returned no match;
the existing blueprint ancestor and precise continuity step are recorded.

The resumed worker also tested direct specialization to the preorder tail,
explicit functor-map reduction, preorder arrow lemmas, and quiver-instance
normalization. Those attempts produced dependent type mismatches or exceeded the
60-second compile limit. They are retained only in the scratchpad. Shared compiler
slot allocation repeatedly starved jobs for many minutes before compilation.

## Second reading by T2

1. **Visible interface — PASS.** Compared the delivered main module and existing
   node with the repository using `diff`. The existing theorem's full signature is
   byte for byte identical. There are no definition changes, new hypotheses,
   weakened conclusions, visibility changes or public-import changes. The only
   new declaration is the separately documented coherence theorem; it has its own
   module and node. No change record is required.
2. **Proof and axioms — PASS as a decomposition.** `lcompile.py --all` compiled
   both delivered modules without errors or warnings. The main module has no
   `sorry`; the new public named coherence theorem has the one reported `sorry`.
   Neither file contains a forbidden declaration or a hollow definition. Explicit
   `#print axioms` in scratch copies showed only `propext`, `Classical.choice`,
   `Quot.sound` and `sorryAx`. The latter is expected from the documented helper
   and existing open dependencies; this is not an axiom-free completed target.
   The tail, inclusion, restricted diagrams and cocones are real constructions;
   no data is chosen from an unproved existence theorem.
3. **Split statement — PASS.** Read the new theorem, its natural-language proof
   and its complete node. Mapping identities and composites, then proof
   irrelevance for the equality witnesses, gives exactly its two conclusions.
   Empty preorders give vacuous conclusions, singleton preorders give the original
   laws, and nonskeletal preorders still use functoriality without identifying
   distinct objects. The theorem has no directedness, geometry, limit, colimit
   or cohomology conclusion, so it is strictly smaller than the item rather than
   a restatement. Independently searched with Lean Finder for "inverse image sheaf
   transition maps functor restriction composition coherence", Loogle for
   `Functor.map_comp`, and Mathlib grep for compatible functor-pullback families;
   the hits concern section families, not these inverse-image transition laws.
   Also searched `lean/Sheaf` and `lean/WeilConjectures` for reindexing/restriction
   coherence. No existing exact theorem was found. Two short attempts using the
   original laws directly, with and without restricted transparency, exceeded the
   60-second file limit; neither attempt is in the delivery.
4. **Route and pruning — PASS after import repair.** Checked the affine comparison
   declaration, the Mathlib finality/whiskering leaf, and `dag/units/sk-thm-p1.json`
   including its `realized` fields. The proof constructs the directed final tail,
   transfers the two universal properties, supplies affineness at every tail
   stage, and applies the existing affine comparison. It keeps the unit route;
   no realized unit statement or step is bypassed. The existing dependencies all
   remain used. Removed three redundant direct Mathlib imports, all publicly
   reachable through the unchanged TopologicalInvariance import. The report now
   records their removal and explicitly distinguishes it from module pruning.
5. **Nodes — PASS.** The existing node changes only `proof`, `proof_deps` and
   `proof_origin`. Both nodes' Lean signatures match the delivered source, and
   each `proof_deps` is exactly the union of its proof steps' `uses`. The new node
   includes source, proof, origin, searches, split status, creation record,
   blueprint ancestry, chapter, unit and Lean record. Its equations are precisely
   the two remaining obligations in the main proof.

Second-reading changes: removed the three redundant Mathlib imports and an extra
blank line; corrected the import and pruning report; added this independent review.
The mathematical proof and all theorem signatures were retained.
