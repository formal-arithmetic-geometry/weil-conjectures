## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-representable-proper-fppf-target-test.json`, `citations.json`, and this report. The sandbox was empty of node files and reports; the item was copied from the current read-only repository. No repository file, Lean file, launcher script, compiler or git command was touched. `prepare.py` is a sandbox-only authoring script.

## New nodes

None: 0 new nodes, 0 Mathlib leaves. All supporting results already exist in the DAG.

Attachments: none. The exact blueprint tag and the concepts representable/proper were searched in `lean/WeilConjectures/`; there is no project declaration giving this result. Mathlib's ordinary scheme results do not constitute an attachment or a leaf for algebraic stacks.

WANTED: none.

The item statement and statement dependencies are unchanged. Its source is Stacks `stacks-properties.tex`, Tag 04XD, `lemma-check-property-covering`, specialized to properness and a scheme W. The source's proof writes `{T ×_Y V → T}` as its fppf covering: the bottom-left arrow in the displayed diagram is actually `T ×_Y W → T`. The proof here uses that arrow, then refines it to a scheme cover. This is a proof typo only, not a statement dispute.

The missing material was a proof, not another assertion of the target-test criterion. I supplied the argument from the existing algebraic-space base-change and descent theorems. There are no unfinished parts of this one-level split.

## Searches and blueprint

I read AGENTS.md, the worker role and brief, the stage-1 document, GOAL.md, the three levels and tool-lemma rule in SETUP.md, STATE.md's stage information, tools/README.md, and delivery-errors B through E. There is no repair note for this item. I read the chapter and unit records and the latest blueprint's `sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. The latest direct-images proof (3) uses compactification and proper-image preservation. The item is an inherited supporting geometric lemma along the alteration/stable-moduli chain recorded in its blueprint.from.place; this delivery does not replace that route or edit the unit. `blueprint_refs.py ancestor` returns None, so the inherited null ancestor and via chain remain. `blueprint_refs.py search 'proper fppf'` gives zero matches. The broader `proper` search and whole-DAG source-tag/concept searches led to the existing supporting nodes, rather than to a new copy of the stack target-test assertion.

Whole-DAG searches included 04XD, lemma-check-property-covering, lemma-descending-property-proper, lemma-base-change-proper, 0422, proper/fppf/fpqc combinations, and the statements of the space-locality and stack-calculus nodes. The field-only `lem-sfb-representable-stack-fppf-locality` covers affine/finite-type/quasi-finite/separated, not properness over arbitrary S. `lem-sfb-space-representable-proper-tests` assumes representability by schemes and is a different test. `lem-sfb-representable-stack-property-tests` concerns DM stacks representable by schemes. None is silently applied outside its hypotheses.

The item's prior Mathlib searches are retained. Five new searches were run using the required msearch.py command and read: LeanFinder (two distinct phrasings), Loogle, grep, and LeanSearch. Their exact queries and results are recorded in the node and searches.jsonl. The hits are scheme-level IsProper, flat descent and morphism-property descent instances. I read Mathlib/AlgebraicGeometry/Morphisms/Proper.lean, especially the Scheme variables and IsProper definition at lines 40–44 and its base-change instances, and the relevant FlatDescent.lean instances. They do not apply directly to arbitrary algebraic-space sources or stack targets. No unrun search or unavailable-service verdict is invented.

## Not duplicates

No new node is created, so there are no new/existing-node pairs requiring distinction. The existing algebraic-space properness nodes are cited, not copied.

## Review by NL

I read Stacks Tag 04XD (`lemma-check-property-covering`) and the list in Section 04XB specifying that properness is among the allowed properties. Its hypotheses allow an arbitrary base scheme S; its W may even be an algebraic space, so the item's scheme W is valid. The definition in spaces-morphisms.tex immediately before `lemma-proper-local` is separated + finite type + universally closed, exactly the intrinsic notion used by the item and the cited locality node. I read Tag 04WP (`lemma-base-change-proper`) and Tag 0422 (`lemma-descending-property-proper`) in their .tex sources, and the scheme refinement described in spaces-topologies.tex `lemma-refine-fppf-schemes`. I also read algebraic.tex Tags 0300 and 045C for the representability/base-change setting, and the etale and fppf covering calculus in spaces-topologies.tex. No SGA source is used.

Step 1 uses precisely the conclusion of lem-sfb-space-proper-base-change. The first evaluation at W is the item's own definition of properness; the cited theorem justifies further scheme tests of V → W. Its source and base-change morphism may be arbitrary spaces, so it does not impose representability by schemes.

Step 2 uses def-trf-algebraic-space for the existence of a representable surjective etale scheme atlas U → B and def-sfb-stable-pointed-moduli-groupoids for the triples and tautological isomorphism. A and B are spaces by the scheme tests in the two explicit representability hypotheses, not by an unstated theorem about every stack map. Choosing the atlas and naming the projections are elementary. I checked the base is the arbitrary T → Y throughout, rather than W or S.

Step 3 reads the flat/lfp/surjective hypotheses on p at this particular T. The bridge in lem-sfb-fibred-groupoid-representable-smooth-calculus explicitly identifies etale/surjective scheme charts with the corresponding properties as maps of fibred groupoids. The statement of lem-sfb-stack-chartwise-smooth-etale-calculus explicitly gives etale ⇒ smooth ⇒ flat and lfp, composition, and surjectivity composition. These are exactly what is needed for U → B → T. Algebraic spaces with their discrete fibred groupoids are algebraic stacks, and these two maps are representable by algebraic spaces; no source-local properness is asserted. Finally def-pc-fppf-site defines a covering of the scheme T by flat lfp jointly surjective scheme maps. The singleton U → T fits it. No fpqc claim about a non-quasi-compact singleton is used.

Step 4 is elementary using the actual triple definition in def-sfb-stable-pointed-moduli-groupoids: the forward map composes alpha with beta inverse and the inverse composes with beta. They fix u and are inverse on compatible arrows and restrictions. The statement of lem-trf-space-fibre-products-etale-covers provides sheaf fibre products as categorical fibre products of spaces; only its existence clause is used, not any questionable stronger representability assertion. Maps between discrete groupoids make this a space isomorphism. Thus the comparison is over U, as required for the subsequent base change, and is stronger than an identification of geometric fibres.

Step 5 first applies lem-sfb-space-proper-base-change along U → W, and then the properness clause of lem-sfb-space-flat-proper-fp-locality. I opened the latter's statement: its three properties are separate, so flatness and finite presentation of A → T are not required. Its descent clause specifically permits an algebraic-space source, scheme target T and fppf scheme family. Those are exactly the objects constructed above. The change under the explicit isomorphism is justified directly from the defining properness clauses. Quantification over all T then concludes the item's definition, without appealing to the target theorem again.

Every cited node's statement was opened; citations.json has one verbatim quote for each of the ten uses, tested as a substring of that statement. The union of step uses is exactly proof_deps. Each step is under 800 characters; no long step hides a new lemma. I checked the transitive statement/proof closures of the reused properness-locality and calculus inputs: none reaches this item. The off-unit fibre-product result is a generic tool, declared in split_report.tool_uses for the maintainer's review.

Small cases: if T is empty, B and its atlas can be empty and the singleton empty-to-empty map is a covering; descent and all products still apply. If Y is nonempty, an empty W cannot satisfy the stated surjectivity hypothesis. Identity covers reduce to direct base change. If X is empty over nonempty Y, the empty projections remain proper and the proof does not require nonempty sources. Non-scheme algebraic-space fibres cause no scheme-representability assumption: the explicit atlas is used only on B. Automorphisms of Y are retained in beta and the triple comparison, so no illicit replacement of a 2-fibre product by a product of point sets occurs.

Corrections made while checking: I refined the algebraic-space cover to a scheme cover, rather than applying the existing scheme-family locality theorem to B → T itself; I wrote the beta-inverse formula to fix the orientation of the 2-isomorphism; and I cited the existing chart/representable bridge instead of assuming it from a definition. The imported statement needed no correction.
