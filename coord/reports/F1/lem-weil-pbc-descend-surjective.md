# Delivery report

1. Files written:

   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-surjective.json`: item split into five proof steps following Stacks Limits Tag 07RR; status `split`.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-chevalley-image.json`: new statement node, Mathlib verdict `mathlib` via `AlgebraicGeometry.Scheme.Hom.isConstructible_image`.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-limit-eventual-empty-basechange.json`: new statement node for Stacks Limits Tag 05F3, Mathlib verdict `no match`.
   - `dag/nodes/sec-proper-base-change/lem-weil-pbc-limit-contained-constructible.json`: new statement node for Stacks Limits Tag 05F4, Mathlib verdict `no match`.

2. Attachments:

   None.

3. WANTED:

   None. The cited Stacks source files are present in `literature/stacks-project/`; the source locations and tags are recorded in the nodes.

4. What was wrong in the prior node/history:

   The original node was unsplit despite carrying only the imported source paragraph. The repaired split makes the finite-presentation reduction, Chevalley image, base-change image identification, use of surjectivity, and finite-stage constructible containment separate named steps. The 05F3 and 05F4 additions are statement-only nodes, as required for newly created Stage 1 nodes; neither hides proof steps. The source statement and its dependencies were retained.

5. What could not be finished:

   No Lean was written or compiled, as required for Stage 1. `python3 tools/review_split.py lem-weil-pbc-descend-surjective` passes. `python3 tools/check_dag.py` reports six pre-existing unreachable nodes outside this delivery; it reports zero cycles and no errors involving this item or its three new nodes.

## Review by F1

I reviewed the item against Limits Lemma 07RR in `literature/stacks-project/limits.tex`, Situation 081D, and the cited Chevalley Lemma 054J and finite-stage constructible Lemmas 05F3/05F4. The first step correctly uses quasi-compactness and quasi-separatedness of the source and target to turn locally finite presentation into the finite-presentation hypothesis used by Chevalley. The second step is exactly the constructible-image assertion and is attached to the Mathlib declaration with matching hypotheses. The third step identifies the image after each base change with the inverse image of the original image, including the limit base change, and the fourth translates surjectivity of the limit morphism into containment of the limit projection in that image. The fifth applies 05F4 and returns surjectivity at a finite stage. I checked each proof dependency against the cited node statements, and verified that the new 05F3 and 05F4 records are complete statement nodes with three-category Mathlib searches and no embedded proof. The review script passes; no Lean or compilation changes are included.
