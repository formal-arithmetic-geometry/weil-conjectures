# Stage-1 delivery: lem-per-preaisle-transfinite-monomorphism-closure

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-preaisle-transfinite-monomorphism-closure.json`: existing statement, now split into six proof steps; no whole-item Mathlib match. The statement is unchanged. The proof is a transfinite induction, with a bar construction and finite horizontal skeleta at limit ordinals.
- `citations.json`: one verbatim current statement quotation for every step/node citation.
- `report.md`: this report.

New DAG nodes: 0. New Mathlib leaves: 0. The preserved `searches.jsonl` and `search-*.txt` were read; successful item searches were added verbatim to `mathlib_searches`, without rerunning unchanged questions. Inherited Mathlib searches were retained. Empty search output files were not treated as successful searches.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag, item id, preaisle, and transfinite found no declaration stating this result. The transfinite-plus sheafification and monomorphic quasi-isomorphism results are different assertions. No upstream-master sorry declaration was treated as a finished proof.

## Wanted literature

WANTED: a general published reference for closure of cocomplete preaisles in Grothendieck derived categories under arbitrary small filtered homotopy colimits/transfinite extensions, for this item, as requested by its inherited source field. This is not a gap in the delivered argument: its bar and telescope proof is written out and marked `proof_origin.by = agent`. The blueprint's Step 2 is motivation, not a purported source proving this auxiliary lemma. Stacks `derived.tex`, Tag 093W (`lemma-compute-colimit`), supplies the telescope model underlying the explicit general-category calculation; Tag 0152 (`lemma-derived-canonical-delta-functor`) supplies the short-exact-sequence triangle through its existing DAG node.

## Problems corrected

The earlier sandbox contained a split and citation file but no report. Its use of `lem-kun-complex-colimit-hocolim` was invalid for the stated generality: that node assumes abelian sheaves or module sheaves on a site, whereas the item assumes an arbitrary Grothendieck abelian category. I replaced that citation with the existing general `lem-kun-sequential-telescope-mono`, and wrote the cokernel universal property explicitly. The telescope exact sequence then gives the needed triangle through `lem-weil-pbc-complex-ses-triangle`.

The earlier telescope step invoked extension closure on a third object without spelling out rotation and the positive shift. The delivered step rotates to the triangle with middle object `Q(B)` and endpoints `Q(W)` and `Q(W)[1]`. This uses exactly the assumed positive-shift closure. The bar-column quotient sign is also explicit: vertical differential `(-1)^(n+1)d` agrees with the quotient column shifted by `[n+1]`.

I restored the existing, already specified `blueprint.from.place` from the current repository, retaining its ancestor and via chain. No protected metadata was intentionally changed. The statement needs no correction and is not disputed.

## What remains unfinished

Nothing in this one-level split. The reused nodes retain their current status and are not resplit here. This worker made no Lean edits, compiled nothing, changed neither the shared repository nor launcher, ran no git command, and started no other agent.

## Review by Q29

I read the worker brief, stage-1 contract, the three blueprint levels in SETUP, GOAL, dag-sync, and delivery-errors B through E. I read the chapter and unit records for `sec-deligne-laumon-a1` / `sk-p-dl-a1-perverse`, and the current `lem-per-artin-gabber-affine-curve.proof.md`, especially Step 2. This item is an auxiliary lemma below the unit, not its key statement, so no unit realization fields change. The argument preserves the set-generated-aisle route motivating the middle t-structure; generic category-theory tools from other units are declared in `split_report.tool_uses`.

I compared the preserved sandbox with the current repository item. I retained its unchanged statement, bar-resolution idea, inherited search results and logged searches. The initial dry run was allowed to exit before any further invocation; it reported the missing `## Review by Q29` report section and performed no push. The present report records the mathematical repair independently of that mechanical failure.

For step 1, I read `lem-weil-pbc-complex-ses-triangle`: it explicitly covers every degreewise short exact sequence in any abelian category, not just sheaves or bounded complexes. Monicity gives the asserted quotient sequence; the induction assertion supplies its first end, and the item's hypothesis supplies its third end. The zero stage and successor argument are genuine parts of the item, not delegated clauses.

For step 2, I read the statements of `def-sp-grothendieck-abelian`, `def-sc-preorder-bar-total`, `lem-kun-grothendieck-derived-coproducts`, and `lem-sc-preorder-bar-filtered-augmentation`. I also read the available bar-total and filtered-augmentation source files and the derived-coproduct module in the shared repository, read-only. The augmentation theorem explicitly has no bound on the complexes. Here its preorder is small, nonempty and filtered, and the Grothendieck assumption gives the exact colimits it requires. Every finite string of ordinals is indexed in the specified universe. The coproduct theorem concerns arbitrary unbounded complexes in the same general Grothendieck category, so it gives the claimed derived coproducts. The existing coproduct module's sorry is not presented as a finished proof or an attachment; its named DAG statement is the cited tool.

For step 3, I checked the bar total's degree `q-p` and vertical sign `(-1)^p` against `def-weil-abstract-derived-category`'s shift convention. Horizontal faces lower the retained column index, proving the skeletal subcomplex assertion. Removing lower columns kills the horizontal part and leaves exactly the positive shifted column. The cited short-exact-sequence theorem then gives the induction triangle. This is a short explicit calculation from existing definitions and triangles, not a hidden new lemma.

For step 4, I opened `lem-kun-sequential-telescope-mono` and checked its full statement. It assumes an abelian category with filtered colimits preserving finite limits; the Grothendieck exactness assumption implies this, and its natural-number/finite-subset indices meet the required size restriction. Its statement gives precisely monicity of identity minus successor, even without monic transitions. I read Stacks Tag 093W and its finite-initial-telescope proof. The delivered step does not assume the sheaf-only homotopy-colimit comparison: it proves the cokernel property in each degree, using `def-weil-pbc-category-colimit` and the explicit partial sums of `def-sc-preorder-bar-total`. Thus the resulting short exact sequence really is in the arbitrary category of the item.

For step 5, I reread the general derived-coproduct statement and the short-exact-sequence triangle statement, and read the rotation axiom in `def-weil-triangulated-category`. They give, respectively, membership of `Q(W)`, a distinguished triangle, and its rotation. Positive-shift closure gives the other endpoint. Extension closure applies to the middle object only after this rotation. For step 6, the localization definition explicitly inverts quasi-isomorphisms; strict fullness is an assumption of the item and transfers membership across that isomorphism. No unmentioned direct-summand or negative-shift closure enters.

I checked the zero ordinal, a single successor, the first countable limit, and larger limit ordinals (including uncountable cofinality). The ordinal bar construction handles the large index set, while only the column filtration is sequential. Thus no countable-cofinal-subsequence assumption is hidden. Zero diagrams and unbounded internal complexes satisfy the same formulas. Empty coproducts are included by the cited coproduct theorem. Repeated closure under `[1]` gives exactly the nonnegative column shifts.

Against delivery-errors B–E: there are no new nodes with unstated objects, proofs hidden in statements, unrun search records, duplicate Stacks tags, or clauses of the item renamed as lemmas. Whole-blueprint searches for preaisle and transfinite monomorphism closure found no duplicate blueprint statement; the monomorphism search returned unrelated nodes. All non-elementary inputs of each step are cited statements, not arguments borrowed from another node's proof. Every quotation in `citations.json` is copied directly from the current cited statement. All six proof steps are below 2000 characters; the only inline identifications are the explicit skeletal differential and elementary cokernel universal property. The statement has not been weakened, no SGA source is used, and no dependency was introduced merely to hide the whole conclusion. Server dry-run diagnostics, including the cycle and route checks, are the remaining mechanical validation before push.
