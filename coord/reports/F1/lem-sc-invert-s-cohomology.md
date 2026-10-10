1. Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology.json` — item, statement node, split proof.
- `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology-affine-case.json` — statement, Mathlib no match.
- `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology-gluing.json` — statement, Mathlib no match.
- `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology-induction.json` — statement, Mathlib no match.

2. Attachments: none. No sorry-free slopmaster2 declaration carries 09MR or this item (searched the item tag, theorem wording, and cohomology/localization terms in `WeilConjectures`).

3. WANTED: none; the Stacks source is available in the machine's literature checkout as `coherent.tex`.

4. The unsplit item had the complete 09MR statement but no proof decomposition. I kept its hypotheses and localization map unchanged. I split the source proof at its actual logical boundaries: affine base case (01XB, 01PV, 01PW), Mayer–Vietoris comparison and five-lemma (01EB, 05QB), and induction principle (08DR). The new nodes are statement-only, as required for nodes not themselves split. Whole-DAG and blueprint searches found no existing node stating these inputs and no blueprint node duplicating them. I tested the statement on the affine case p > 0 (both groups vanish) and p = 0 (the usual section localization map), and on s = 0 where the principal open is empty and the degree-zero localization has the corresponding zero comparison.

## Review by F1

I read the item source in `coherent.tex`, Lemma 09MR (`coherent-lemma-invert-s-cohomology`), including the p = 0 remark, affine case, Mayer–Vietoris diagram, and final induction invocation. I also read the source passages for Lemma 08DR and the tags 01XB, 01PV, 01PW, 01EB, and 05QB. Step 1 cites the affine-case node, whose statement explicitly gives the localization isomorphism and vanishing used. Step 2 cites the gluing node, whose statement explicitly supplies the hypotheses on U, V, U intersect V and the conclusion on U union V; the node statement also names the open-localization identities and five-lemma that the step uses. Step 3 cites the induction node, whose statement exactly supplies the conclusion from the affine and gluing hypotheses. No step is marked elementary because each invokes a nontrivial Stacks theorem. Each new node is self-contained, carries the correct Stacks source and hypotheses, has statement-only proof fields, records LeanSearch plus Loogle/LeanFinder plus Mathlib-source grep, and has no Mathlib match. The item and all new nodes carry the ancestor blueprint reference and exact `from.place`; `citations.json` quotes literal substrings of the cited statements.
