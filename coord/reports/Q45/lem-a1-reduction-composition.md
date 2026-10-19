## Worker report

1. Files written: `dag/nodes/sec-deligne-laumon-a1/lem-a1-reduction-composition.json` (item, statement unchanged, split proof); root `citations.json`; and this report. No new DAG nodes were created. The retained `searches.jsonl` records the actual LeanSearch, LeanFinder, Loogle, and Mathlib grep queries. No Lean, compiler, Lake, live project, or launcher file was written.

2. Attachments: none. I searched the project source for the item id, blueprint tag, title, and finite-map/cohomology terminology. No sorry-free declaration states this item. The item's Lean audit remains `none`.

3. WANTED: none.

4. The imported proof cited `lem-a1-finite-map-cohomology` for the derived comparison after replacing \(\mathcal F\) by \(j_!\mathcal F\). That existing node states only the degreewise cohomology comparison for a lisse sheaf on the source curve, so it does not supply the derived comparison for the extension-by-zero sheaf. I removed that citation and expanded the item's one proof step: the compact-support identification is by the definitions of extension by zero and compact support; properness and compact-support composition come from `prop-functor-package`; exact finite direct image and \(Rg_*=g_*\) come from `lemma-weil-pbc-finite-direct-image-exact`. The weight and lisse hypotheses remain exactly in the item statement for the downstream affine-line argument.

5. Nothing remains unfinished in the split. The item is ready for the required server dry run and delivery.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs.

## Review by Q45

I read the current item node, the current main-20261015 blueprint statement and proof, the chapter record `sec-deligne-laumon-a1`, and the unit record `sk-thm-dl-a1-upper`. I also read the complete statements of `lemma-weil-pbc-finite-direct-image-exact`, `prop-functor-package`, and the retained `lem-a1-finite-map-cohomology` node. The item statement introduces \(C_0\), \(C'_0\), \(g\), \(j\), \(\mathcal F\), and \(\mathcal K\) exactly as the blueprint; its two statement dependencies provide the ordinary compact-support and punctual-weight conventions. I checked the source's finite generically étale hypothesis and the finite-complement/dense-open hypotheses, and I did not add any hypothesis.

The sole proof step follows the blueprint's finite-map transport paragraph. It uses the finite-direct-image node for exactly its two stated clauses: finite \(f_*\) is exact and \(Rf_*=f_*\) on bounded-below complexes. It uses the functor-package node for exactly its compact-support composition \(R(gf)_!\simeq Rg_!Rf_!\) and proper coincidence \(Rf_!\simeq Rf_*\). The step applies these to the proper finite \(g\) and the sheaf \(j_!\mathcal F\), then takes cohomology. The two citation entries in `citations.json` are verbatim substrings of those node statements.

I checked edge cases relevant to the transport: \(j\) may have empty finite complement (then \(j_!\mathcal F=\mathcal F\)); \(g\) may be the identity finite map; and the displayed derived isomorphism immediately gives the degreewise \(H_c^i\) isomorphism for every integer \(i\). The punctually pure weight condition is carried by the statement but is not needed for this formal transport step, as in the source. Mathlib searches used all required query kinds and returned only generic properness, sheaf-pushforward, or unrelated compact-support hits; no Mathlib declaration states this Weil-sheaf derived comparison. No SGA source is cited. No new node or duplicate was introduced.

