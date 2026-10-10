1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-fp-module-map-descent-affine.json`: split statement, no new nodes.
- `citations.json`: verbatim citations for all three proof steps.

2. Attachments: none.

3. WANTED: none.

4. The item is exactly the affine ring theorem used by Limits Lemma 01ZR. I checked the statement against Algebra Lemma 05N7, including all three clauses. No duplicate node exists in the DAG; the related module-colimit nodes concern sheaves or different fixed-ring statements. No sorry-free project declaration states this theorem.

## Review by F1

I read `/home/ubuntu/c1-stacks-review/algebra.tex` at Algebra Lemma 05N7 and its proof, and the affine paragraph of Limits Lemma 01ZR in `/home/ubuntu/c1-stacks-review/limits.tex`. Step 1 uses the finite matrix presentation and the element-representation clause of `lem-pc-filtered-colimit-commrings-elementwise`; the finite matrix and cokernel calculation is the source's explicit construction. In repaired Step 2, the target presentation `A_i^p -> A_i^q -> N_i` is explicit: a relation image that is zero in the target cokernel is written as `R_N b_t`, the finitely many entries of each `b_t` are lifted by clause (1), and the coordinate equalities `d_t - R_N b_t = 0` are forced at a later stage by clause (2). The same presentation and witness argument is used in repaired Step 3 for each generator difference, so no coefficient is incorrectly claimed to vanish in the ring itself. The directedness and finite-presentation hypotheses are used where stated; no Noetherian assumption is needed in the affine ring lemma. I checked zero-rank presentations and the zero module as edge cases. The required Mathlib searches were run for the item with `msearch.py`: LeanSearch was unavailable; LeanFinder found only generic filtered-colimit infrastructure, Loogle found no matching declaration, and the Mathlib grep found no finite-presentation module descent theorem.

5. What could not be finished: nothing.

## Second reading by F1

- Step 1 checked against Algebra Lemma 05N7 (Tag 05N7), clause (1), and `lem-pc-filtered-colimit-commrings-elementwise`; verdict: the finite matrix presentation and elementwise colimit representation are the cited facts, with no uncited non-elementary assertion.
- Step 2 checked against Algebra Lemma 05N7 (Tag 05N7), clause (2), and `lem-pc-filtered-colimit-commrings-elementwise`; verdict: the target relation matrix is explicit, each zero cokernel element is expressed as `R_N b_t`, and only the finitely many resulting coordinate equalities are equalized at a later stage.
- Step 3 checked against Algebra Lemma 05N7 (Tag 05N7), clause (3), and `lem-pc-filtered-colimit-commrings-elementwise`; verdict: each generator difference is treated as a zero cokernel element and equalized using a lifted relation witness, rather than by asserting its ring coefficients vanish.
- The item statement checked hypothesis by hypothesis against Algebra Lemma 05N7 (Tag 05N7) and the affine part of Limits Lemma 01ZR (Tag 01ZR); verdict: all three clauses agree, including zero-rank and zero-module cases.
- The sole node file checked for B1-B7: statement only, self-contained definitions, TeX, source tag and label, and recorded searches; verdict: compliant. It is the intended affine ring lemma and is not a duplicate of another DAG node.
- The returned E3/E5 defects were repaired by adding the target relation presentation and the `R_N b` witnesses in Steps 2 and 3; the report records the source, citation, duplicate, edge-case, and Mathlib checks. The repaired dry-run delivery preflight printed `OK (not pushed)`.

- Metadata rechecked against the delivered item: corrected the new node's stale `created.item` from `lem-pc-fp-module-map-descent` to `lem-pc-fp-module-map-descent-affine`; no mathematical statement or proof step changed.
