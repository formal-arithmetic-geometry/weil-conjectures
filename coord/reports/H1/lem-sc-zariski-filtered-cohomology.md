1. Files written:

- `dag/nodes/sec-smooth-purity/lem-sc-zariski-filtered-cohomology.json`: statement split, no new nodes, Mathlib searches recorded.
- `citations.json`: verbatim quotes for every cited node in each proof step.

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` states this Zariski result exactly; the nearby `Scheme.H_map_isColimit_of_isFiltered` declaration is sorry-bearing and is the etale-site statement attached to another node.

3. WANTED: none.

4. What was corrected: the imported proof cited an etale hypercover theorem and an etale filtered-colimit lemma for a Zariski-site conclusion. I replaced that route with the existing general topological theorem `lem-sc-topological-filtered-cohomology`, which exactly supplies filtered-colimit continuity once its basis hypotheses are checked. The Noetherian-scheme node `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` supplies the underlying Noetherian-space condition; the remaining facts that every open in a Noetherian space is quasi-compact and that intersections remain open are written in step 1. Step 2 explicitly specializes to the quasi-compact open `U=X` and uses `def-sc-topological-abelian-cohomology` plus `def-sc-zariski-cohomology` to identify both cohomology notation and the canonical colimit map. I searched the whole DAG and blueprint for duplicates before creating no nodes. The item was tested on the empty scheme, a one-point scheme, and a finite discrete Noetherian scheme; all reduce to exact global sections and the claimed map is the evident colimit isomorphism.

## Review by H1

I read the item source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/lem-sc-zariski-filtered-cohomology.md`, the existing general theorem `lem-sc-topological-filtered-cohomology` (Stacks 01FF), the Noetherian-scheme minimal-closed-subset node (Stacks 01OZ), and the two Zariski/topological cohomology definition nodes. Step 1 uses the cited Noetherian statement for the underlying space and the cited topological theorem for the exact basis and intersection hypotheses; the Noetherian-topology consequences are the elementary open-subset argument. Step 2 uses exactly the general theorem's canonical map at `U=X`, then the cited definition statements to identify open-site cohomology with `H^q(X_Zar,-)` and preserve the coprojection-induced map. I verified every citation quote against the corresponding node file and kept all hypotheses explicit. The Mathlib searches were run with LeanFinder, Loogle, and source grep; they found only generic sheaf/site infrastructure and no matching theorem. No new node was needed, so there are no new-node duplicate or statement checks beyond the existing cited nodes.

## Second reading by H1

- Item statement: checked against the blueprint lemma and the filtered-colimit conclusion of Stacks 01FF; the Noetherian-scheme, filtered-system, degree, and canonical-isomorphism hypotheses/conclusion agree.
- Step 1: checked against the statements of `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` (01OZ) and `lem-sc-topological-filtered-cohomology` (01FF); the Noetherian-space consequences used to establish a quasi-compact-open basis and quasi-compact intersections are valid, and all theorem-level dependencies are cited.
- Step 2: checked against the 01FF conclusion at the quasi-compact open `U=X`, plus `def-sc-topological-abelian-cohomology` and `def-sc-zariski-cohomology`; the cohomology groups and coprojection-induced canonical map are identified without changing direction or degree.
- New nodes: none; the existing theorem and definition nodes were checked for exact quoted statements, so B1-B7 and duplicate/Mathlib-leaf checks introduce no additional node.
- Edge cases: the empty scheme, a one-point scheme, a finite discrete Noetherian scheme, and degrees `q=0` and `q=1` satisfy the same specialization (global sections in degree zero and the stated colimit map).
- Changes: none to the node or citations; this second reading adds only this audit record. The dry-run delivery preflight passes.
