# Delivery report

1. Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-etale-cohomology-invariance-under-site-equivalence.json` — statement, split proof, and metadata; no new nodes.
- `citations.json` — verbatim statement excerpts for every cited node at every proof step.

2. Attachments: none.

3. WANTED: none.

4. Issues found: the item was unsplit and had no Lean declaration. Its imported statement and hypotheses are coherent with the definition of cohomology over an object. The proof needed to make explicit that the induced sheaf equivalence is additive and that injective resolutions are transported; these are supplied by existing DAG nodes rather than hidden assumptions.

5. Nothing remains unfinished.

## Review by H1

I read the item node, the unit `sk-prop-cd`, and the source references to Cohomology on Sites Lemma 03YU and Sites Lemma 03A0. I also opened the complete statements of `lem-weil-pbc-site-equivalence-sheaf-transport`, `lem-weil-pbc-equivalence-injective-resolutions`, and `def-weil-pbc-sites-and-cohomology`. Step 1 uses exactly the first node's assertion that precomposition with an equivalence and the induced topology is an equivalence of sheaf categories. Step 2 uses the definition's injective-resolution computation and the second node's three clauses: injectives, exact sequences, and resolution-level functoriality. Step 3 uses those same resolution and cohomology statements; the section identity is the direct evaluation formula for precomposition, and compatibility with object morphisms is sectionwise naturality. I checked that the object `W` is in `C`, that `e(W)` is the corresponding object in `D`, and that all `q >= 0` cases are covered, including degree zero. No new node was created, so there were no new Mathlib or small-case obligations. The imported blueprint place was filled explicitly in the item metadata and the split report.
