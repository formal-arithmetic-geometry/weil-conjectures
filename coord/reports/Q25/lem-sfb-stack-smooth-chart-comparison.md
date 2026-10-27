# Stage-1 delivery: lem-sfb-stack-smooth-chart-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-stack-smooth-chart-comparison.json`: statement node, now split; statement and statement dependencies preserved. Mathlib: no exact match or one-line specialization.
- `citations.json`: 18 verbatim statement excerpts, one for each step/node citation.
- `searches.jsonl`: actual searches performed with the prescribed msearch command. Existing searches in the item were retained.
- `prepare.py`: sandbox-only preparation script, not part of the delivery.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the blueprint tag and smooth-chart, algebraic-stack, Deligne--Mumford and source/target-locality concepts. The hits are scheme, ring or deformation-space statements, not the assertion about properties of morphisms of stacks. No sorry-free declaration stating the item was found.

## WANTED

None. All sources used for this split are present as Stacks TeX or current blueprint text.

## Findings and corrections

The imported statement is faithful to Stacks 06FM, including the extra smoothness requirement on the induced map in (A). Its explicit pointwise locality hypothesis is Stacks 06F8. The statement was not changed. In particular, no extra quasi-separatedness, finite-type or representability assumption on the original stack morphism was introduced.

The item previously had no proof. The new proof constructs the middle comparison spaces and identifies the exact cartesian square; it does not assume that an arbitrary map between smooth charts is smooth. The map that must be smooth is a base change of the induced map required in (A). The pointwise locality hypothesis itself then finishes the comparison. This is the same argument as 06FM, with the elementary consequences of 06F8 applied directly instead of packaging 06F9/06FA as extra nodes.

Both scheme conditions are included in a cycle of four implications. This avoids silently asserting that a map from a scheme to an algebraic space is representable by schemes. The source of the comparison may be a space throughout. For the representable clause the comparison square after base change to a scheme is written explicitly. Fppf locality is an allowed additional hypothesis but is not needed by this particular argument: the stronger pointwise source-and-target locality already gives the descent used in that square.

The inherited blueprint ancestor is null: `blueprint_refs.py ancestor lem-sfb-stack-smooth-chart-comparison` prints `None`. The original precise `from.place` and `via` chain are retained. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and its direct-images statement/proof (snapshot main-20261023-1620). The current direct-images proof (3) passes through proper direct image and the open-coefficient theorem; the older alteration/moduli details occur only in the inherited dependency chain. This delivery supplies its local stack comparison prerequisite without changing the unit or chapter route. Blueprint-wide searches for `smooth local`, `algebraic stack`, `source-and-target`, and `atlas independent` found no blueprint statement of this general comparison.

## Unfinished work

None within the one-level split. The cited nodes retain their own existing states. No Lean was written or compiled.

## Not duplicates

No new nodes. Whole-DAG searches for 06FM and 06F8 found the item and its finite-type/local-quasi-finite users or specializations, not an independent theorem that should replace this proof.

## Review by Q25

I read Stacks `stacks-morphisms.tex`, Tag 06FM (`lemma-local-source-target`), including the whole comparison diagram, its cartesian subsquare and final representable paragraph. I also read `spaces-descent.tex`, 06F8 (`definition-local-source-target`), 06F9 (`lemma-local-source-target-implies`) and 06FA (`lemma-local-source-target-characterize`), and `criteria.tex`, 076V (`lemma-stacks-etale`). No SGA source is used. There are no new nodes whose source or hypotheses need a separate review.

For step 1, I opened `def-sfb-stable-pointed-moduli-groupoids`, `lem-sfb-stack-chartwise-smooth-etale-calculus`, and `lem-sfb-etale-smooth-atlas-fppf-descent`. The first gives the actual groupoid 2-product and the representable diagonal/etale atlas; the second explicitly says etale maps are smooth; the third has exactly the etale-stack, representable-diagonal and smooth-surjective-atlas hypotheses and concludes fppf descent. Thus the etale convention does not leave a hidden change of stack notion.

For step 2, I opened `lem-sfb-dm-etale-atlas-calculus`. Its statement supplies the DM 2-fibre product and an etale scheme atlas. The chartwise calculus explicitly supplies smoothness, base change, composition and surjectivity for representable maps. Applying it to the chosen target atlas and then the source atlas proves that the resulting source map is smooth surjective. The resulting diagram satisfies the additional induced-map smoothness in (A), so restricting (A) to schemes is legitimate.

For step 3, I opened `lem-sfb-representable-pullback-over-space` and read its statement: it allows an arbitrary space as base, not merely a scheme. The two maps to which it is applied are the original representable vertical charts. I checked its source `algebraic.tex` 0300 (`lemma-base-change-by-space-representable-by-space`). I opened `lem-trf-space-fibre-products-etale-covers`: its first assertion supplies the remaining space fibre product. The 2-product identification is proved from the triples specified by the groupoid definition, not imported from a definition of scheme products. The DM atlas lemma justifies the DM nature of the intervening pullback. The only nontrivial smooth map into the middle space is the base change of the induced smooth map from the arbitrary (A) diagram. I checked both projections to the compared target are smooth and that the projection to the arbitrary source is surjective by the exact base-change/composition assertions of the chartwise calculus.

Step 4 is a direct use of the item's own hypotheses (ii), then (i), then (iii), on the spaces already constructed in step 3. For each source point, surjectivity supplies the required point above it. The target chart need not be surjective, exactly as in hypothesis (iii). Thus no unrecorded smooth postcomposition/descent lemma is needed. This is marked elementary because the entire inference is three applications of stated assumptions after step 3, not a claim about smoothness of a new map.

For step 5, I opened `def-trf-scheme-algebraic-space`; it explicitly makes the actual Yoneda scheme into an algebraic space. Restriction/inclusion of quantifiers yields two of the arrows in the cycle; steps 2 and 4 yield the others. For space-valued source and target I checked that the identity diagram is admissible and, in the reverse direction, that the hypothesis on the induced map supplies exactly the precomposition to which (i) applies. This covers both directions without invoking the proof of 06FA as a black box.

For step 6 I checked every fibre product against the representability hypothesis and the space-valued-base theorem. The map $G_0\to H$ is the base change of $h$ along $H\to V$, rather than a base change along an incorrectly chosen projection. Its two vertical maps are base changes of the original $a,b$, with surjectivity only on the left. Arbitrary-base-change stability is used here, precisely where smooth-base-change stability would not suffice. Pointwise locality then applies to the space map $Z\to T$. Step 7 checks the reverse implication on an actual scheme atlas of the target; the space atlas supplied by the definition of algebraic space is a scheme, its map is etale hence smooth, and the original source map is smooth surjective by the cited calculus.

I checked the statements against empty sources, identity morphisms, schemes viewed as spaces, and a nonrepresentable DM morphism such as a finite etale classifying stack over a field. An empty source forces the locality condition vacuously and admits an empty source atlas, so the implications remain valid; no target surjectivity was accidentally used for an arbitrary (A) diagram. The classifying-stack example confirms that $\mathcal X\times_{\mathcal Y}V$ must be allowed to remain a stack until an atlas is chosen; the proof never treats that object as a space except under the final explicit representability hypothesis. The empty target forces the source empty, so creates no exceptional case. I also checked there is no dependency path from any cited node back to this item.

Every proof step is shorter than 2000 characters (lengths 679, 606, 1039, 574, 757, 1043, 688). The displayed 2-product identification is a pointwise rearrangement of the named defining triples, not a hidden general comparison theorem. No clause was moved into a new lemma. I reviewed delivery-errors B--E: this delivery adds no nodes, has no Mathlib-leaf claim, preserves TeX and hypotheses, cites statements rather than their proofs, exposes the induced-map hypothesis in the comparison, and records the sole off-unit tool (space fibre products) in `split_report.tool_uses`. The citations were copied verbatim from the opened statements and validated locally as substrings.
