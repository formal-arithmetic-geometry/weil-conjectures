1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-inverse-image-section-description.json`: statement split into three proof steps; no new node.
- `citations.json`: verbatim dependency quotes for all steps.

2. Attachments: none.

3. WANTED: `literature/stacks-project/etale-cohomology.tex`, Lemma Tag 09XN (lemma-describe-pullback), proof paragraph beginning “By construction of g_{i, small}^{-1}G”, for the item. The repository contains the citation metadata but not the source text, so the proof is marked agent-written while following that cited paragraph.

4. The imported item had an empty proof. I checked the inverse-image definition in `lem-weil-pbc-etale-inverse-image-algebraic-structures`, the local sheafification representative statement in `lem-weil-pbc-site-sheafification-sections-local`, and the filtered-colimit element statement in `lem-weil-pbc-filtered-colimit-sets-elementwise`. Each cited statement says the precise fact used by its step. The factorization is obtained from the pair defining the colimit, and the etale covering is supplied by the sheafification lemma. I also ran the required Mathlib searches; LeanSearch was unavailable, while LeanFinder and grep found no exact Mathlib theorem.

## Review by E1

I read the item source citation and the three cited node statements. Step 1 uses the inverse-image node's explicit sheafification of a colimit presheaf, including its pairs `U' -> U x_V W`; step 2 uses the sheafification node's explicit local representative covering; step 3 uses the filtered-colimit node's assertion that every colimit element comes from one stage, together with the inverse-image node to identify that stage with an etale object and a morphism into its base change. The scheme and sheaf hypotheses in the item are exactly those required by the inverse-image definition. I checked the identity case `g = id` (the covering may be the identity and the representative is the original section) and the empty scheme case (the assertion is vacuous). I corrected the initially empty proof by making the presheaf, sheafification cover, and colimit representative explicit, and did not create a duplicate local-section node because the existing sheafification node already states it.

5. Nothing remains unfinished except the unavailable bundled literature file noted above; the cited Stacks paragraph is represented by the complete three-step argument.
