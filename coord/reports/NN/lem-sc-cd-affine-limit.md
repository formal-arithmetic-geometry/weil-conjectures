# Stage 1 report

1. Files written: `dag/nodes/sec-smooth-purity/lem-sc-cd-affine-limit.json` (statement, split, 0 new nodes); `citations.json`; this report. No Mathlib leaves.
2. Attachments: none.
3. WANTED: none.
4. The imported item had an uncited finite-presentation descent input and an uncited use of cohomology continuity in step 2. I repaired the proof dependencies and retained the existing finite-data descent node rather than creating a duplicate auxiliary node. The statement itself was unchanged.

## Review by NN

I read the item source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-sc-cd-affine-limit.md`, the chapter and unit records, and the statements of every cited node. Step 1 uses `lem-weil-pbc-etale-finite-data-descent`, whose statement explicitly supplies descent of finite étale diagrams, morphisms, equalities, and coverings at a common stage; it also uses `lemma-weil-pbc-etale-cohomology-continuity` for the stated inverse-system hypotheses. Step 2 now explicitly cites that continuity theorem, whose statement gives the filtered-colimit isomorphism for cohomology. Step 3 cites the filtered-colimit cohomology theorem and the torsion filtered-union theorem; their quoted statements provide exactly the two operations used. I checked the qcqs and affine-transition hypotheses against the item and the continuity node, verified that no new node was merely a clause of the item, and ran all required Mathlib searches (LeanSearch unavailable; LeanFinder, Loogle, and grep found no matching theorem). The only correction was adding the missing proof citations and filling blueprint provenance.

## Second reading by NN

- Item statement: checked against the blueprint node and its source text hypothesis by hypothesis; the inverse-limit, qcqs, affine-transition, and uniform torsion-dimension clauses agree, including zero and field cases.
- Step 1: checked against `lem-weil-pbc-etale-finite-data-descent` clauses for finite-presentation objects, morphisms, equalities, and coverings, and against cohomology continuity; repaired the missing finite-data dependency and citation.
- Step 2: checked that continuity applies to the torsion sheaf `p_i^*F_i` on each stage and that the bound gives vanishing for every `q>c`; added its missing `uses` entry.
- Step 3: checked the filtered-colimit cohomology theorem and the torsion filtered-union theorem; expanded the two colimit applications so the vanishing argument is explicit.
- No new nodes: the finite-data descent input is an existing DAG node, and no elementary, duplicate, restatement, or Mathlib node was introduced.
- Small cases checked: the zero sheaf gives the zero colimit; for a field and for `n=1`, the fixed-exponent argument specializes directly; the empty scheme has vanishing cohomology.
- Blueprint provenance keeps `from: null` for the imported node and `same_as: []`; `split_report.blueprint` identifies the three proof paragraphs.

Changes: added the existing finite-data descent node to Step 1 and `proof_deps`, added continuity to Step 2's `uses`, expanded Step 3, added matching citation quotes, and checked blueprint provenance.

Dry-run repair: restored `blueprint.from: null` as required for an imported node. Expanded Step 2 to check explicitly that direct image and inverse image preserve the fixed exponent. Step 1 now invokes the statement of finite-data descent rather than the proof of continuity.

Search-record correction: the first reader's Loogle queries were rejected, so their verdicts are recorded as unavailable rather than evidence of no match. No new-node Mathlib searches are required because there are no new nodes.
