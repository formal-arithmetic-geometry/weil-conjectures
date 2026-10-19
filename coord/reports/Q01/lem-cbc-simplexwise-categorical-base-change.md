1. Files written:

- `dag/nodes/sec-smooth-purity/lem-cbc-simplexwise-categorical-base-change.json` — the item, statement split into five proof steps; no new nodes.
- `citations.json` — verbatim citations for every non-elementary step use.

2. Attachments: none.

3. WANTED: an archived copy of Lurie, *Higher Topos Theory*, Proposition 3.2.2.8 (the HTT PDF was read online on 2026-10-17; the item keeps the source's archival-WANTED note).

4. The imported item had no proof. I checked the statement against HTT Proposition 3.2.2.8 and preserved every hypothesis: arbitrary simplicial sets over an arbitrary base, no fibrancy or injectivity assumptions, and empty simplicial sets allowed. The split follows the source: specialize arbitrary base changes to standard simplices; reduce arbitrary simplicial sets to filtered unions of finite sub-simplicial sets; induct on finite cell dimension and number of nondegenerate simplices; then compare the two pushouts using Joyal left properness. The filtered-colimit and model-category inputs are existing DAG nodes, so no new node was created. I searched the whole DAG and blueprint for a duplicate simplexwise criterion and found none. The blueprint ancestry was retained through `thm-cbc-finite-level-proetale`; this lemma is the auxiliary calculation supporting that proof even though the blueprint does not name it separately.

5. What I could not finish: no archival HTT source is present in `literature/`; the online source was available and is recorded as WANTED. No Lean code or compiler/build tool was used.

## Review by Q01

I read the current item node, its unit and chapter records, the source statement and proof of HTT Proposition 3.2.2.8, and the full statements of `lem-coef-joyal-filtered-equivalences`, `lem-coef-joyal-model-structure`, and `lem-coef-all-cofibrant-left-proper`. Step 1 is the direct specialization of (i) to a standard simplex. Step 2 uses exactly the filtered-colimit closure stated by the filtered-equivalences node; I verified that the finite subobjects are filtered and that degreewise pullback is reindexing of sets over each base degree. Step 3 is the finite-cell induction from HTT, with the pushout and pullback formulas written explicitly; the boundary and simplex inclusions are the relevant monomorphisms. Step 4 uses the Joyal node's cofibration/weak-equivalence classes and all-cofibrancy, then the left-proper node's pushout stability; the cube comparison is the usual repeated pushout-along-a-cofibration and two-out-of-three argument. Step 5 closes the finite and filtered inductions. I checked the empty case, the point-base case, and the case of a degenerate simplex; all are covered by the stated induction or the filtered colimit. The proof dependencies equal the union of the step uses, citations are verbatim, and no statement or coefficient category was changed.

## Second reading by Q01

- Source and item statement: I read HTT Proposition 3.2.2.8 in the online PDF (printed p. 181, PDF p. 199; archival copy remains WANTED) and checked the diagram $X\to Y\to S$, arbitrary $T\to S$, both quantified conditions, and the absence of fibrancy, injectivity, finiteness, and nonemptiness hypotheses clause by clause; verdict: agrees, including empty $T$ and arbitrary base $S$.
- Step 1: checked the implication against the proposition's first sentence; specializing $T$ to $\Delta^r$ with $t=\sigma$ gives exactly (ii); verdict: elementary and correct.
- Step 2: checked the filtered finite-sub-simplicial-set reduction against the proposition's filtered-colimit sentence and the statement of `lem-coef-joyal-filtered-equivalences`; degreewise pullback is reindexing in sets and the finite subobjects are filtered in the slice; verdict: cited input says the required closure.
- Step 3: checked the empty case, top-dimensional nondegenerate-simplex attachment, boundary and simplex pullback pushout formulas, and the two induction parameters against the proposition's induction paragraph; verdict: correct, with no extra hypothesis.
- Step 4: checked the three vertex equivalences against the induction hypotheses and (ii), the cofibration input against `lem-coef-joyal-model-structure`, and left properness against `lem-coef-all-cofibrant-left-proper`; verdict: correct after removing an unwarranted claim that the boundary attaching map is injective.
- Step 5: checked the finite-to-filtered conclusion against the proposition's final sentence and the arbitrary choice of $T\to S$; verdict: elementary and correct.
- New nodes: none. I searched the whole DAG for the proposition's simplexwise criterion and for categorical-equivalence/base-change formulations; the existing Joyal filtered-colimit, model-structure, and left-proper statements are the cited tools, so no duplicate node is needed.
- Edge cases: tested the zero/empty simplicial set, point base, $r=0$ and $r=1$, and a degenerate simplex conceptually; each is covered by the filtered or induction argument and no clause excludes it.
- Searches: independent `msearch.py` runs used LeanFinder (generic base-change property hits only), LeanSearch (Yoneda/standard-simplex declarations only), Loogle (unknown identifier/no exact match), and Mathlib grep (Joyal trick declarations only); none states this full criterion.
- Changes: corrected the split-owned creation stamp's item identity to `lem-cbc-simplexwise-categorical-base-change`; revised step 4 to state only the genuine cofibration $\partial\Delta^r\hookrightarrow\Delta^r$ and to explain the left-proper cube comparison. No source statement, hypothesis, dependency, or citation was otherwise changed.
