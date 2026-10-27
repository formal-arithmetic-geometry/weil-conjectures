## Worker report

Files written:
- dag/nodes/sec-trace-formula/lem-trf-hom-product-stabilization-factorization.json: existing statement node, now split into three elementary steps; Mathlib searches found no exact result or one-line specialization.
- citations.json: []; no step cites another node.
- searches.jsonl: actual search-command log for this item.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.
Attachments: none. The blueprint-id and conceptual searches of lean/WeilConjectures found no declaration giving this result. Existing Mittag-Leffler results concern towers of finite/Artinian modules or sheaves, or inverse-limit exactness; they do not supply the Hom-product factorization assertion for arbitrary modules and directed posets.
WANTED: none.

The statement and its statement dependency are unchanged. Its directed-system identities and its product with componentwise operations already define the only structures used in the proof. I read def-weil-pbc-category-colimit: it defines diagrams and colimits, including the nonempty directed-poset case. It serves only the statement's terminology; neither the existence nor a property of a colimit is invoked in the proof.

The source is literature/stacks-project/algebra.tex, Tag 059E (proposition-ML-characterization), specifically (5) implies (3), lines 21077–21102 in this checkout. I read the proposition and the entire implication. The surrounding finite-presentation hypothesis is unnecessary for this implication. The proof uses only the stated Hom-image equality. The split replaces the source's general componentwise Hom/product identification with the explicit inclusion into one coordinate and projection from it, so no separate Hom/product comparison theorem or choice of a simultaneous family of lifts is hidden.

## Source clarification

The last sentence of this implication treats k at least j and j at least k, leaving incomparable indices implicit. For a general directed partial order these two cases do not exhaust k at least i. Step 3 supplies the missing case: choose a common upper bound ell of j and k and compose the factorization at ell with f_{k,ell}. This repairs a proof omission, not the statement; no STATEMENT-DISPUTED correction is needed.

## Searches and blueprint

I retained the five recorded searches of the imported item and read their recorded hits. I also ran the prescribed logged command for grep, Loogle, LeanSearch, and two LeanFinder phrasings; all services answered. The returned declarations concern direct-limit representatives and their universal maps, image factorizations, and range/kernel identities. I read Mathlib/CategoryTheory/CofilteredSystem.lean (including IsMittagLeffler), Mathlib/Algebra/Module/Submodule/Range.lean (range, mem_range and range_comp), and the module direct-limit maps/lifts in Mathlib/Algebra/Colimit/DirectLimit.lean. None states this implication by one-line specialization. The node records the actual query strings and log summaries, without inventing searches.

I searched the whole DAG for 059E and the product-stabilization/factorization terminology, and used tools/blueprint_refs.py search for factorization and precomposition, together with a full latest-blueprint text search for the Hom-product assertion. The nodes lem-trf-mittag-leffler-hom-systems and lem-trf-mittag-leffler-eventual-domination have different hypotheses and conclusions: respectively tensor Mittag-Leffler implies stable Hom images for finitely presented systems, and tensor Mittag-Leffler is equivalent to eventual tensor-kernel domination. Neither states the present implication from one product-valued Hom system for arbitrary modules. No equivalent imported blueprint statement was found; same_as remains []. No new nodes were created, so there are no new/existing same-tag duplicate pairs.

I read the chapter and unit records and the latest blueprint chapter, unit and ancestor lem-trf-local-term-locality statement/proof. The inherited ancestry passes through lem-trf-ml-countable-colimit; the latest ancestor text does not itself contain this subsequently introduced algebra expansion. The precise supporting Tag 059E place already recorded in blueprint.from is preserved; split_report explains the relationship. No chapter, unit, realization field or route was changed.

## Review by Q106

I checked sections B–E of coord/delivery-errors.md against the actual statement, source and proof. There is no new statement-only node to audit, no extra hypothesis, no new object chosen from a theorem, and no relabeling of the conclusion into a new lemma.

Step 1 cites no node: the statement defines P as the coordinatewise product, so inserting x in coordinate j and zero elsewhere is a linear map by the displayed coordinate checks. Evaluation is linear for the same reason, and projection after insertion is the identity. This is a direct construction, not an uncited categorical product theorem. The only equality test of indices is classical and imposes no finiteness assumption.

Step 2 cites no node: e_j composed with f_ij is in the first image by its witness e_j. Equality of images, exactly the hypothesis at ell at least j, supplies the witness a_ell in the second image. Projecting yields g_ell f_iell = f_ij. The types are M_ell to P to M_j; the source M_i is unchanged. This is unfolding membership in an image and associativity of composition, not a separate lifting theorem. Only one witness is chosen for each current ell, and no assertion of coherent lifts is made.

Step 3 cites no node: directedness supplies ell above both j and k, and i at most j at most ell makes every transition in the formula defined. The identity f_kell f_ik = f_iell is precisely in the statement. The resulting map M_k to M_j can point backwards in the ordering; the claim asks for an arbitrary linear map, not a transition. Thus the fixed j chosen once in Step 1 works for every k at least i, including incomparable k and j. This is a few-line application of the assumptions and Step 2, with no hidden lemma. All three steps are below 2000 characters (indeed their total is below 1500).

I checked the singleton index set (the chosen transition is the identity), zero modules and the zero ring (all formulas still hold), constant systems with identity transitions, and the diamond poset with incomparable j and k (its top index gives exactly Step 3). These tests also show why assuming a linear order or surjectivity/injectivity of a transition would be unwarranted; neither is used. No finite presentation, finite generation, countability, colimit construction, or exactness result is used. The statement is faithfully the (5) to (3) implication with unused surrounding hypotheses omitted.

C1/C4 have no missing citation: each step is explicitly elementary and all its ingredients are definitions or hypotheses in the item or earlier displayed equalities. There are no cited proof nodes to quote, so citations.json is the empty list. proof_deps is the empty union of the three uses lists. The source is a source for the written argument and is not treated as a black-box node. There is no cycle, off-unit theorem use, new Mathlib leaf, or proof longer than the long-step threshold. Nothing remains unfinished mathematically.
