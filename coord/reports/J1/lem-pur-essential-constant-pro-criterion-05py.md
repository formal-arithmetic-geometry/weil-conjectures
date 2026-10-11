1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-essential-constant-pro-criterion-05py.json` — item split; no new nodes; Mathlib searches found no exact match.
- `citations.json` — verbatim dependency quotes for all proof steps.

2. Attachments: none.

3. WANTED: `literature/stacks-project/categories.tex`, Categories Lemma Tag 05PY and Definition Tag 05PU(2), because the checkout contains only citation metadata.

4. No new node was created. The existing `def-pc-essentially-constant-pro-diagram` states exactly the cone, retraction, and eventual-factorization clauses used by the item. The project source was searched for the item id and its concepts; no declaration states it. The blueprint search found no duplicate blueprint node. The Mathlib searches were run through `msearch.py`: LeanFinder returned eventual-constancy colimit declarations but no Stacks pro criterion; Loogle returned zero hits/unavailable; grep found only eventual-constancy APIs; LeanSearch was unavailable.

## Review by J1

I read the item statement, the existing pro-diagram definition, the nearby forward Hom-colimit node, the Stacks citation recorded in the item, and the 05SC citer. Step 1 defines each cone map as the inverse image of the identity representative under the assumed bijection and checks naturality by postcomposition and injectivity. Step 2 checks the retraction by comparing the images of `r ∘ u_{j_0}` and `id_X`; it uses the definition's retraction clause only as the target interface. Step 3 uses equality of representatives in the filtered colimit to obtain the common refinement and exactly the factorization required by the definition. Step 4 matches the resulting data clause by clause to the cited definition and records the characterization of `u_j`. All cited-node quotes are copied verbatim from the dependency statement, and every step is marked elementary because it is a direct identity, naturality calculation, or the defining equality criterion for a filtered colimit. No hypotheses beyond cofilteredness, the stated bijections, and the given `r` were introduced.

5. Nothing remains unfinished in the split.

## Second reading by J1

- Step 1 checked against Categories Lemma Tag 05PY(4), construction of the pro-cone, and the statement of `def-pc-essentially-constant-pro-diagram`; the postcomposition/naturality argument and the colimit representatives are correct and elementary.
- Step 2 checked against Categories Lemma Tag 05PY(4), the retraction clause in Definition Tag 05PU(2), and the cited definition node; the two images under the assumed bijection are equal, so injectivity gives the required identity.
- Step 3 checked against Categories Lemma Tag 05PY(4), its filtered-colimit representative criterion, and the factorization clause of the cited definition; the variance is correctly `J^{op}` and the common refinement gives exactly the required factorization.
- Step 4 checked against Definition Tag 05PU(2) and Lemma Tag 05PY(4); the constructed cone, retraction, factorization, and characterization match the definition clause by clause.
- Existing dependency `def-pc-essentially-constant-pro-diagram` checked against Categories Definition Tag 05PU(2); it is self-contained, has the required TeX and definition dependency, and no duplicate or Mathlib declaration states this notion.
- Small cases checked conceptually: the constant diagram, a one-object category, and the zero/terminal-object cases introduce no extra hypotheses or variance changes.
- No changes were needed after second reading; the source comparison, citations, recorded searches, and blueprint metadata remain correct.
