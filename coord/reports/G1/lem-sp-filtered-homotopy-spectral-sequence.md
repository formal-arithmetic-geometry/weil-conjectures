1. Files written:
   - `dag/nodes/sec-abelian-varieties/lem-sp-filtered-homotopy-spectral-sequence.json`, statement split with three proof steps; no new nodes and no Mathlib leaves.
   - `citations.json`, with verbatim quotations for every cited statement.

2. Attachments: none.

3. WANTED: Weibel, *An Introduction to Homological Algebra*, the filtered-complex homotopy-invariance calculation underlying the E2 comparison (the project literature records the book but does not contain a local text copy).

4. What was checked: the repository node was compared with Stacks Homology Lemma 012O (filtered-complex functoriality) and Definition 012U (convergence). The slopmaster2 source was searched for the item id, its title, and filtered spectral-sequence homotopy declarations; no declaration states it, and the existing Mathlib/project spectral-sequence declarations do not provide this filtered homotopy result. Existing DAG statements were read before splitting: `thm-sp-spectral-object-yields` gives bounded filtered-complex spectral sequences, explicit Z/B page descriptions, natural page homology identifications, convergence, and functoriality; `def-sp-filtration` and `def-sp-convergence` are already built into that theorem's statement. Step 1 uses the theorem's boundedness and functoriality clauses. Step 2 writes the representative calculation: the homotopy has filtration shift -1, so the discrepancy is a page-one boundary and the natural page homology induction gives equality from E2. Step 3 uses the theorem's natural E-infinity/associated-graded identifications and the elementary fact that chain-homotopic maps induce the same cohomology map. The boundedness hypotheses were checked degree by degree; the zero-complex and identity-map cases give the expected equality, and a homotopy with no filtration shift was excluded because it need not agree on E2.

## Review by G1
I read the target node, its blueprint ancestor `thm-sp-grothendieck`, and the Stacks sources for 012O and 012U. I also opened the complete statement of `thm-sp-spectral-object-yields` before citing it. Its boundedness clause supplies Step 1's existence hypotheses, its functoriality clause supplies the page maps, its Z/B formula and natural page homology identification supply Step 2's calculation, and its convergence/naturality clause supplies Step 3's abutment conclusion. No new node was created because the only external non-elementary interface needed by the split is already stated by that existing theorem; the homotopy computation is the proof of this item itself. I verified that every hypothesis on the filtration and every one-step shift on h is used, checked the zero and identity edge cases, and recorded the unavailable LeanSearch service rather than treating it as a Mathlib match.

5. Stage 1 does not require a Lean proof; the split supplies the statement and its proof steps for later formalization.

## Second reading by G1

- Item statement: checked against Stacks Tags 012O (homology-lemma-spectral-sequence-filtered-complex-functorial) and 012U (homology-definition-filtered-complex-ss-converges), hypothesis by hypothesis; verdict: bounded degreewise filtrations, one-step homotopy shift, page-$E_2$ equality, and abutment graded compatibility are all stated explicitly.
- Step 1: checked against clauses (a)--(c) of `thm-sp-spectral-object-yields`; verdict: the degreewise bounds supply both bounded filtered spectral sequences and filtered maps induced by $a$ and $b$.
- Step 2: checked against the cited $Z_r/B_r$ and natural page-homology clauses; verdict: the representative calculation now records the filtration of $d_Cx$, the one-step shift of $h$, the $E_1$ boundary, and the induction from $E_2$.
- Step 3: checked against the convergence and naturality clause of `thm-sp-spectral-object-yields` and the convergence convention in Tag 012U; verdict: the cocycle calculation gives the common cohomology map and natural associated-graded maps.
- New nodes: none; the existing theorem supplies every non-elementary interface, and the filtered homotopy calculation is the item's proof.
- Existing-node search: searched the DAG for the item id, filtered spectral-sequence homotopy phrases, and Tags 012O/012U; no duplicate theorem was found. Mathlib searches remain recorded in the node, including unavailable LeanSearch.
- Edge cases: checked the zero complexes, identity maps, and complexes concentrated in one degree; each reduces to the stated homotopy or identity calculation.

Changes made: corrected `created.item` to this item and tightened Step 2 so the one-step filtration shift is connected explicitly to the $E_1$ boundary and the $E_2$ conclusion. No statement or citation was weakened.
