# Worker report: lem-coef-simplicial-model-target-test

## Files written

- `dag/nodes/sec-six-functors/lem-coef-simplicial-model-target-test.json`: item split into eight proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited dependency in every step.

## Attachments

No sorry-free project declaration states this item. No Lean attachment was found under `WeilConjectures/` in `/home/ubuntu/weil-src-slopmaster2`.

## WANTED

- Archival copy of Lurie, *Higher Topos Theory*, Appendix A, §§A.3.4–A.3.5 (especially Lemma A.3.4.6, Corollary A.3.4.11, and Lemma A.3.5.14). The online PDF was read on 2026-10-17, but it is not present in `literature/`.

## What I checked and changed

The imported statement is retained exactly. It is the essentially-surjective comparison test from HTT A.3.4.6/A.3.4.11 used in the reduction at A.3.5.14, with the explicit no-local-Kan/no-cofibrancy clause. The item had no proof steps, so I supplied the proof without introducing a node that merely restates one of its clauses. I searched the DAG and blueprint for a matching simplicial-model-target statement. The existing `lem-coef-simplicial-fully-faithful-homotopy-image` is the non-surjective fully-faithful essential-image theorem, and its ancestry reaches this item through the inversion/product comparison; using it here would create a cycle. I therefore used its underlying replete-full-subcategory argument directly in two steps.

The proof first replaces endpoints by Bergner cofibrant-fibrant representatives and then uses the existing projective simplicial presheaf model and projective-model-calculus nodes. It computes the enriched Yoneda mapping simplicial sets explicitly, forms the replete full subcategory of presheaves isomorphic to representables, and proves its inclusion is a Bergner fibration. The cylinder argument proves both injectivity and the essential-image factorization criterion directly. Applying the assumed bijection to the Yoneda functor of `X` gives `v` with `vu=1`; applying injectivity to the Yoneda functor of `Y` gives `uv=1`. The final actual-functor assertion uses the existing model-localization detection node, whose weak equivalences are the Dwyer--Kan equivalences in the Bergner model.

## Review by NV

I read the target node, its unit and chapter records, the imported blueprint proof paragraph for `prop-coef-integral-exceptional-adjoint`, HTT Appendix A.3.4.6, A.3.4.11 and A.3.5.14 in the online PDF, and the statements of every cited DAG node. Step 1 uses only the replacement and homotopy-class statements: the first cited node supplies the Bergner model and replacements, the second supplies actual representatives between cofibrant and fibrant objects, and the interval-lifting node supplies Kan mapping sets for fibrant simplicial categories. Step 2 uses the existing projective presheaf model statement and projective diagram calculus exactly for the enriched presheaf category, its cofibrant representables, and its fibrant Kan-valued objects. Step 3 is the elementary enriched Yoneda calculation; its only external input is the projective calculus statement describing enriched mapping simplices and free diagrams. Steps 4 and 5 use the interval-lifting criterion and the homotopy-class cylinder statement exactly as quoted; I checked that repleteness supplies the required object lifts and that the cylinder's weak equivalence is a Dwyer--Kan equivalence. Step 6 uses only the Bergner localization statement to pass from the fully faithful Yoneda calculation to the replete representable subcategory. Step 7 uses the derived-pushout-mapping node for the induced component functor and its natural-isomorphism ambiguity, then the Step 6 factorization criterion to obtain `v`; essential surjectivity of `pi_0 u` is used precisely here. Step 8 uses the model-localization detection node and the Bergner localization node to identify an invertible class with an actual Dwyer--Kan equivalence.

I checked the edge cases used by the statement: empty `X` forces `Y` empty under essential surjectivity; identity maps give the evident bijections; and the proof uses essential surjectivity only to force every value of $F$ into the replete representable subcategory. Without that hypothesis this inference is unavailable; this report makes no claim that all maps omitting an object fail the model-target tests. No hypothesis of local Kan mapping sets or cofibrancy is imposed on the original `X,Y`; those properties occur only after the explicitly stated replacements. Every proof step is below the 2000-character long-step threshold. The Mathlib searches already logged for the item found only general simplicial-category/model-category APIs, never this enriched detection theorem; the fresh required searches for the prospective presheaf support were run and found no exact match. No SGA source was used.

## Continuation check

I retained the prior proof, citations, and logged search results, compared the sandbox item with the current shared node, and ran the required initial dry run: it passed at `9ccbfb5991`. I then added the explicit SM7 application with initial-to-cofibrant and fibrant-to-terminal maps to justify the local Kan property of each model-target subcategory; this is a direct specialization of the exact projective-calculus statement already cited in step 2. I also corrected the report's unsupported assertion about arbitrary maps that are not essentially surjective: the proof only requires essential surjectivity at its stated factorization step. There are no new nodes, duplicated statements, or changes to the imported statement. The supporting references are the existing DAG statements quoted in `citations.json`; the literature reading and Mathlib results recorded by the prior attempt were retained.
