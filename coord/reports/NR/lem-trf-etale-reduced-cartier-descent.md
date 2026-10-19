1. Files written:
- `dag/nodes/sec-trace-formula/lem-trf-etale-reduced-cartier-descent.json` — statement, split into three proof steps; no new Mathlib leaf.
- `citations.json` — verbatim statement quotes for every cited node in every step.

2. Attachments: none. No sorry-free declaration in the project states this item exactly.

3. WANTED: none.

4. The imported item was unsplit. I checked the source statement against Stacks Tags 083C, 034E and 01J3, and checked the existing reduced-induced-subscheme, étale-reducedness, closed-immersion base-change, flat Cartier pullback, invertible-ideal, and fpqc module-descent nodes. Step 1 uses the closed-immersion base-change ideal formula, étale stability under base change, the existing theorem that an étale scheme over a reduced scheme is reduced, and uniqueness of the reduced induced structure; the support is the inverse image by the fibre-product topology. Step 2 verifies the hypotheses of flat pullback because étale morphisms are flat and identifies the pulled-back ideal. Step 3 follows Tag 083C: refine the covering by affine étale opens, use the effective-Cartier/invertible-ideal equivalence, reflect finite locally free rank one by fpqc descent, then return to effective Cartier. I checked the empty divisor separately: its ideal is the unit ideal.

5. What I could not finish: no Lean or compiler work was permitted in this stage. The split is ready for the required server dry run.

## Review by NR
I read the item node, the unit `sk-i-curve-zero`, the chapter `sec-trace-formula`, the source passages for Tags 083C, 034E and 01J3, and every node cited in the three proof steps. The reduced-pullback step takes exactly the closed immersion and ideal image from `lem-pc-closed-imm-base-change`, reducedness from `etale-proposition-etale-reduced`, and uniqueness/support from `lem-weil-pbc-reduced-induced-closed-subscheme`; none is used for a fact outside its statement. The forward Cartier step uses the effective-Cartier definition, flat pullback, and the flat clause of the étale definition. The converse uses the base-change ideal formula, the two existing Cartier/invertible equivalences, and the fpqc descent statement that reflects finite local freeness of rank one. I corrected the imported node by adding complete proof steps, proof dependencies, blueprint ancestry, and citations; I also checked the empty scheme/divisor edge case.
