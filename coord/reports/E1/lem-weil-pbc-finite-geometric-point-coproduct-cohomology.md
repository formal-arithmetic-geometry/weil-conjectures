1. Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-finite-geometric-point-coproduct-cohomology.json`: statement, 2-step proof, and split metadata.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-geometric-point-cohomology.json`: new unsplit statement node; Mathlib search verdict no match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-finite-coproduct-cohomology-assembly.json`: new unsplit statement node; Mathlib search verdict no match.

2. Attachments

None. No exact sorry-free declaration or blueprint duplicate was found.

3. WANTED:

None; the Stacks etale cohomology source is present locally.

## Review by E1

I read the item source and the parent blueprint proof, then checked the Stacks source `literature/stacks-project/etale-cohomology.tex` at Theorem 03QT, Lemma 03QU, Section 03QQ, and the first paragraph of Lemma 0A5B. Step 1 cites the new single-point node, whose statement exactly supplies vanishing in positive degrees and the degree-zero stalk identification. Step 2 cites the new finite-coproduct assembly node, whose statement exactly supplies the finite product of component cohomology groups, and applies Step 1 to every summand. I verified that the index set is finite, each summand is open and closed, and the stalks are the chosen geometric stalks. I searched the DAG and blueprint for both statements and searched Mathlib by LeanSearch, Loogle, and source grep; no existing declaration or Mathlib theorem matched. I tested the statements on the empty coproduct and on a singleton coproduct, where the formulas reduce respectively to zero products and the single-point calculation.

5. What was wrong or corrected

The imported item had no proof. I supplied the component calculation and made the finite-product assembly an explicit cited statement so that the proof does not hide the non-elementary coproduct decomposition.

6. What remains

The two new statement nodes are intentionally unsplit queue items, as required for a one-level split.
