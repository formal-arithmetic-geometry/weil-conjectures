1. Files written:
- `dag/nodes/sec-picard-framework/det-picard-main-geometry.json`: split item; no new nodes (all supporting statements already exist).
- `citations.json`: verbatim statement quotes for every proof-step citation.

2. Attachments:
- None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this three-clause item exactly.

3. WANTED:
- None; the proof follows the obtained Stacks Project source `literature/stacks-project/pic.tex`.

4. What was wrong in the imported node: the statement used `H_g` without introducing it, so I made it a scheme representing `Hilb^g_{C/k}` and added `thm-pc-hilb-curves` as a statement dependency. The imported proof listed `thm-pc-picard-representable` in `proof_deps` but did not cite it in a step; step 1 now cites it where the group structure and representing scheme are used. The geometric-irreducibility argument now explicitly uses the existing geometrically-integral Hilbert node, surjectivity after base change, and irreducible continuous images. The existing `lem-sc-group-scheme-separated-field` supplies separatedness. I checked that every cited node says the quoted fact and that all hypotheses (algebraically closed implies separably closed, smooth proper geometrically integral curve, degree `g`, and field extensions) are present.

5. What I could not finish: nothing.

## Review by Q104

I read the item source `literature/stacks-project/pic.tex`, Tag 0BA0 (`lemma-picard-pieces`), including the paragraphs proving the open translate cover, Abel morphism and surjectivity, properness, geometric irreducibility, and translation between degree components. I also read each cited DAG node. Step 1 uses the representability/group-scheme statement, the open smooth pure-dimension chart, the twisting lemma, and the closed diagonal theorem for group schemes over fields; their statements provide exactly those interfaces. Step 2 uses the Hilbert representability/properties, the universal-divisor-to-Picard morphism, Riemann–Roch for a degree-`g` line bundle, and the already stated surjectivity lemma; the algebraically closed field and geometric-point argument match the hypotheses. Step 3 uses properness of `H_g`, the image-universally-closed criterion, geometric integrality of every Hilbert base change, surjectivity preserved by base change, irreducibility of continuous images, and the degree-translation isomorphism. I corrected the missing `H_g` introduction and the omitted representability citation, and checked all citation quotes verbatim in `citations.json`.
