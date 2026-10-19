# Stage-1 report: lem-pur-twist-sheaf-locally-free

Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-twist-sheaf-locally-free.json` — existing twelve-step statement split retained, status changed to `split`; no new nodes, hence no Mathlib leaves.
- `citations.json` — one verbatim statement quote for every cited node in every proof step.
- `report.md` — this review.

Attachments: none. No sorry-free declaration in the checked project source states the item exactly; the source declaration `AlgebraicGeometry.Scheme.pur_twist_sheaf_locally_free` and its auxiliary declarations contain `sorry` and therefore are not attachments.

WANTED: Serre, *Local Fields*, for the valuation-ring input used in the existing coefficient-extension argument (the existing node `lem-weil-l-adic-extension-integers-dvr` records this source need).

The repository copy already contained the complete split and its blueprint ancestry. I retained its statement, twelve proof steps, dependencies, searches, blueprint fields, and prior review metadata, changing only `status` from `unsplit` to `split` for delivery. No new node was created: all cited identifiers already exist in the DAG, and the item is not a restatement of any one dependency.

## Review by Q99

I read the item node, chapter `sec-smooth-purity`, unit `sk-def-sf-admissible`, the blueprint ancestor `def-coefficient-twists-detailed`, and the source module `lean/Sheaf/Paper/PurTwistSheafLocallyFree.lean`. The source theorem and all listed auxiliary declarations still contain `sorry`, so they cannot close or attach this item. The item statement has the four intended clauses: finite-level roots, the completed root line and reductions, finite coefficient extension, and derived-complete constructibility/support.

For steps 1–4 I checked the cited root-of-unity, site-comparison, Kummer, weakly-etale localization, inverse-limit, and completed-constant statements directly in their node files. Step 1 uses only the finite etale root trivialization, the etaleness of the represented root scheme, and the constant-coefficient comparison to transfer the trivialization to the pro-etale site. Step 2 applies Kummer on each test object and uses local lifting to prove transition epimorphisms. Step 3 uses a fixed weakly contractible pro-etale cover, local section lifting, and the constant-sheaf stalk criterion to construct compatible primitive roots. Step 4 defines the completed action coordinatewise and invokes the stated quotient property of the completed constant coefficients; the tensor-with-a-quotient calculation is written explicitly.

For steps 5–8 I read the valuation-extension, finite-quotient, DVR finite-free, completed-coefficient, geometric-point-lifting, and localization node statements. Step 5 explicitly proves finite generation and torsion-freeness before applying the cited DVR criterion. Step 6 compares completed coefficient sheaves through a finite basis and a cofinal subsequence, rather than commuting tensor with an arbitrary inverse limit. Step 7 identifies the integral tensor line and its ordinary reductions using the completed quotient formula. Step 8 checks finite-level local triviality and finite stalks after choosing a coefficient exponent divisible by the ramification index.

For steps 9–12 I read the K-flat, integral-derived-reduction, finite-torsion-constructibility, support, derived-limit, and derived-complete definitions and theorem statements. Step 9 proves K-flatness after restriction to the local free cover and computes the derived reduction in degree zero. Step 10 verifies constructibility and the support inclusion, including the empty-scheme edge case. Step 11 uses the explicit quotient tower and the cited surjective-tower derived-limit criterion to establish derived completeness with the correct transition maps. Step 12 checks that the resulting degree-zero line satisfies the detailed integral derived-complete category definition.

I checked every `uses` entry against the cited node statement and generated `citations.json` with verbatim quotes for all 30 dependency identifiers across the 12 steps. I also inspected the long steps for hidden sublemmas: each is one continuous construction or calculation whose auxiliary facts are cited, so no additional node is needed. The blueprint `from` field, source places, Mathlib search log, and existing tool-use declarations were retained. Small edge cases checked include rank-one roots, quotient levels, ramification-divisible exponents, and the empty base in the support clause.

What I could not finish: none within stage 1; no Lean code or compiler/build tool was run.
