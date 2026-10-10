1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-dvr-saturation-line.json` — statement, split proof, and split report.
- `dag/nodes/sec-picard-framework/lem-sc-dvr-saturation-line-smith-normal-form.json` — Mathlib leaf; exact match to `Submodule.exists_smith_normal_form_of_le`.

2. Attachments: none. No sorry-free slopmaster2 declaration states the item or the new node exactly (searched `WeilConjectures/` and `Comparator/` by the item id and the relevant saturation/Smith-normal-form terms).

3. WANTED: none. The Stacks source is cited by tag; the local literature checkout contains citation metadata but not the generated `.tex` source file.

4. The imported item was unsplit and had an empty proof. I kept its statement and its existing `def-sc-discrete-valuation-ring` dependency. The new node is strictly smaller: it records only the Smith normal form fact for a submodule of a finite free PID module, and carries no proof sketch because it is a Mathlib leaf. I searched the whole DAG and blueprint before creating it; no duplicate Smith-normal-form or DVR-saturation node was found.

## Review by F1

I read the item node and the `sk-thm-picard-rr` unit route, including the rank-induction paragraph of `lem-sc-riemann-roch`, and checked the statement against Stacks Tag 0CC4. The three proof steps follow that paragraph. Step 1 uses only the definitions of tensoring with the fraction field and intersection: a common denominator gives a nonzero element of the intersection, and the displayed implication proves saturation. Step 2 uses the new Smith-normal-form leaf; its cited statement supplies bases and diagonal inclusion, while the two inclusions after tensoring are checked directly, so the generic rank is exactly one because the line `Ks` is one-dimensional. Step 3 uses the same cited diagonal statement and the saturation from step 1: a nonunit diagonal factor would create nonzero torsion in `E/L`, which saturation rules out, so all factors are units and the quotient has the remaining `r-1` basis vectors.

For the new node I read Mathlib `Mathlib/LinearAlgebra/FreeModule/PID.lean` lines 483–503, where `Submodule.exists_smith_normal_form_of_le` has exactly the finite-free PID hypotheses and diagonal-basis conclusion recorded. I ran LeanSearch (service unavailable), Loogle, and a source grep; the latter two found the exact declaration. I tested the item on `r=1` (the quotient is zero), on `R^2` with `s=(1,0)`, and on `R^2` with `s=(1,t)/t`; in each case the intersection is a rank-one saturated summand and the quotient is free of rank one. No statement or hypothesis was corrected.
