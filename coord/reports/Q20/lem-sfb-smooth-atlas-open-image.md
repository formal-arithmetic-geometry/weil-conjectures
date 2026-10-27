## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-atlas-open-image.json`, the item, now split, with unchanged statement and statement dependencies; `citations.json`, with one verbatim statement quotation for each step/dependency pair. No new nodes and no new Mathlib leaves.

Attachments: none. Searches of `lean/WeilConjectures/` by the exact blueprint id and by `open.image.substack`, `smooth.atlas`, and `AlgebraicStack` found no project declaration stating this construction. Scheme smoothness alone does not attach this item.

WANTED: none. The needed Stacks source files are available locally.

The imported node had an empty proof, not an incorrect statement. Its source uses the fppf convention; the item uses the etale-stack convention. The split proves etale descent directly and checks the representable diagonal and atlas, instead of silently applying an fppf-only theorem to an etale stack. No target or statement was changed. The inherited blueprint ancestor is null: `tools/blueprint_refs.py ancestor lem-sfb-smooth-atlas-open-image` explicitly returned None. Its detailed `from.place` and `via` are retained. The current blueprint file was read under `literature/blueprint/latest/`, including direct-images proof (3); no older snapshot was used as the operative blueprint.

Nothing remains unfinished in this one-level split. The supporting statements already have DAG nodes; no additional queue items are needed.

## Searches and reuse

Read AGENTS.md, SETUP.md including the three levels, GOAL.md, the stage-1 brief and stage document, worker role, STATE.md, tools README, the chapter and unit records, and delivery-errors.md B--E. There is no repair note for this item and there was no earlier sandbox item or report to resume.

The DAG was searched by source tags 05UP, 076V, 01VC and by open-substack, universally-open, smooth-composition and base-change notions. The relevant nodes were opened and their statements read, including the invariant-open descent and representable-fibred-category stack nodes. We use the direct 05UP image construction rather than mistakenly treating V as an invariant open in U: it need not be invariant. Whole-blueprint searches for `open substack`, `smooth atlas` and `05UP` found zero matches. The existing chartwise calculus and universal openness nodes provide the non-elementary smoothness/open-image inputs. The general point-image theorem is reused from `lem-a1-space-point-open-calculus`; no duplicate is created.

Five actual msearch.py calls are in searches.jsonl and copied verbatim as tool/query/result records into the item: LeanFinder with two different phrasings, Loogle with `"Stack", "IsOpenImmersion"`, grep with `AlgebraicStack|open.image.substack|smooth.atlas`, and LeanSearch for constructing the open image substack of a representable smooth morphism. All services answered. The returned declarations concern schemes: smooth open immersions, scheme open ranges, and scheme images. None handles a stack or its full-subgroupoid image, so none is an exact match or a one-line specialization for the item. The older Q85 searches in the item were retained as history; no unrun search was invented.

## Not duplicates

No new nodes were created. In particular, no extra 05UP node restating the item or an individual conclusion was introduced.

## Review by Q20

I read `stacks-properties.tex`, Tag 05UP, lemma-open-image-substack, from its statement through its final surjectivity argument. The item is its scheme-atlas specialization with an explicit scheme-pullback image clause. I also read `morphisms.tex`, Tag 01VC (open immersion smooth), `algebraic.tex`, Tag 05UN (representable fibred category over a stack is a stack/algebraic stack), `criteria.tex`, Tag 076V (etale convention), `spaces-morphisms.tex`, Tag 042S (flat locally finitely presented maps universally open), and `spaces-properties.tex`, Tag 03H4 (surjectivity from points of the fibre product to matching point pairs). There are no new-node sources to certify.

Step 1 uses the actual clause (1) of `lem-weil-pbc-etale-composition-cancellation`, not a definition of etaleness, to make the open immersion etale. The statement of `lem-sfb-stack-chartwise-smooth-etale-calculus` supplies etale implies smooth and composition for representable maps. The open immersion is scheme-representable by inverse-image opens. Both U and V are schemes, so these are legitimate algebraic-stack inputs; no smoothness or surjectivity of j is assumed in advance.

Step 2 uses the same calculus node for arbitrary base change and smooth implies flat and locally of finite presentation. Those are the exact hypotheses in `lem-sfb-flat-lfp-space-universally-open`. That node supplies openness for algebraic spaces, not only for schemes, and no quasi-compactness is needed. The open-subscheme structure on the resulting open subset of T is the restriction in `def-weil-open-immersion`.

Step 3 uses the fibre-product triples from `def-sfb-stable-pointed-moduli-groupoids` to identify E_(xh) with E_x times_T T'. I checked that `lem-a1-space-point-open-calculus` explicitly states the arbitrary-base-change image equality; its theorem is not restricted to etale morphisms. Thus it applies to the smooth map E_x to T and arbitrary h. Merely citing an etale-image theorem would have been insufficient. Equality of open subschemes comes from the same open subset, not from equality of closed scheme images.

Step 4 is the direct verification of the defined full subcategory's stack property, using the stack definition in `def-sfb-stable-pointed-moduli-groupoids`. Pullback stability is already proved in step 3. Isomorphism sheaves are inherited by full faithfulness, and object descent follows because a jointly surjective etale cover detects whether an open subset is the whole base. This does not invoke 05UN with the wrong topology, nor assume algebraicity of W in advance.

Step 5 checks the entire groupoid of lifts, not just its isomorphism classes. The fibre-product definition gives its triples and the unique arrow alpha' alpha^{-1}. `lem-weil-pbc-morphism-factors-through-open-subscheme` explicitly supplies the unique scheme-map factor through an open subset containing the image. Its hypotheses hold for h:T' to T with image in I_x; no analogous assertion for arbitrary locally closed strata is used. The preferred object xh proves essential surjectivity of the displayed equivalence with h_(I_x). This supplies exactly the pullback image clause of the item.

Step 6 uses the diagonal tuple as a section, so factorization of g through W is constructed as an object over V. Full faithfulness gives V times_W T equal to V times_X T with its original projection. Smoothness is already known from step 2; surjectivity is the defining predicate of W, so it is tested for every scheme T mapping to W, not just at geometric points of one atlas. No unproved cancellation of smoothness across an open inclusion is used.

Step 7 checks the diagonal by full faithfulness and by the given diagonal of X. The already constructed smooth surjective scheme atlas then proves algebraicity in exactly the item's etale convention. I checked the small cases V empty, V=U, empty test scheme, and a proper open V whose image is nevertheless all of X (for instance a two-component atlas of a point restricted to one component). The construction gives respectively the empty open, all of X, the empty pullback, and all of X; it never incorrectly identifies W's pullback to U with V. Nothing assumes V is nonempty, invariant, affine, quasi-compact, or surjective over X.

C1/C4 were checked against the statements themselves; citations.json records exact substrings for all 14 citation pairs. Every non-elementary input is a named existing node. C5 duplicate searches and the transitive dependency check found no dependency back to the item. B1--B7 are vacuous for new nodes; the item retains self-contained TeX and all original fields. D1/D2 are avoided because no assertion is moved to a new restatement node: the proof carries the image construction, descent and atlas checks. E1--E7 required no statement correction. All seven steps are shorter than 2000 characters; the elementary steps only assemble prior results and unfold the stated stack/groupoid definitions. The only textual correction while checking was removing an accidentally escaped apostrophe from the last step.

The point-image node, the scheme open-factorization node, and the open-immersion-etale node are generic tools from other units. Their exact uses are declared in split_report.tool_uses for the maintainer's review; no top-level maintainer-owned tool_uses field was written. They supply geometric tools under the same blueprint prerequisite, not a different finiteness route.
