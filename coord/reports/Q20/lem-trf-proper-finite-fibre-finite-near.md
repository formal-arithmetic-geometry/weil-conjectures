1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-proper-finite-fibre-finite-near.json`: existing statement node, split proof, Mathlib searches retained and supplemented by the required Q20 searches; no new node and no Mathlib leaf.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

2. Attachments: none.

3. WANTED: none.

4. What was wrong or incomplete: the imported item had an empty proof. I filled it from Stacks Tag 02UP, preserving the statement's absence of a Noetherian hypothesis. The proof uses the existing DAG nodes for properness, finite-fibre quasi-finiteness, the open quasi-finite locus, restriction to open subschemes, and proper plus locally quasi-finite implies finite. No duplicate or clause node was created.

## Review by Q20

I read the item and the exact Tag 02UP statement and proof in `literature/stacks-project/more-morphisms.tex`, and checked the chapter `sec-trace-formula` and unit `sk-i-curve-zero`. Step 1 uses `pqf-lem-proper-basic` for finite type, local finite type, and universal closedness, and `pqf-lem-locqf-fibre-discrete` for quasi-finiteness at each point of the finite fibre; those statements contain exactly these conclusions. Step 2 uses `lem-sc-quasi-finite-points-open`, whose statement gives both the open locus and local quasi-finiteness of its restriction. Step 3 uses the universally closed clause of `pqf-lem-proper-basic` and the elementary complement construction. Step 4 uses `lem-pc-proper-base-change` for properness after base change to the open neighbourhood, `lem-weil-pbc-lqf-restriction-to-opens` for local quasi-finiteness on the inverse-image open, and the Mathlib leaf `pqf-lem-proper-lqf-finite` for finiteness. I verified that the finite-fibre hypothesis is used only at the chosen point, that the complement image is closed, that the chosen open contains the point, and that no Noetherian assumption enters. I also checked the required Mathlib search outputs: LeanFinder and LeanSearch returned only related global proper/finite declarations, Loogle returned no exact declaration, and grep found no neighbourhood theorem; therefore the item is not a Mathlib leaf. No Lean source declaration with the blueprint tag gives this item.

5. What I could not finish, and why: nothing remains for stage 1.
