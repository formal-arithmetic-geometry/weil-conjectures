1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-rhom-cohomology-ext-ring.json`: statement node, split into three proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-rhom-one-point-hom-complex.json`: statement-only node, Mathlib verdict no match.
- `citations.json`: exact quotes for every cited node in every step.

2. Attachments: none.

3. WANTED: `literature/stacks-project/more-algebra.tex`, Section `section-RHom`, equation `equation-h0-RHom` (Tag 0A64), for the derived internal-Hom/Ext comparison. WANTED: `literature/stacks-project/derived.tex`, Lemma Tag 06XR, for the injective-resolution computation of Ext. The source TeX is not present in this clone; the proof is written from the cited statements already recorded in the DAG.

4. What was wrong or incomplete: the imported item had an empty proof and did not expose the one-point specialization needed to pass from the sheaf-valued derived internal Hom definition to the ordinary module Hom complex. I searched the whole DAG, blueprint index, and Lean source; no node or declaration states that specialization. The existing `lem-weil-pbc-ext-via-injective-resolution` does state the remaining Ext computation, so I cited it rather than duplicating it. No statement was changed.

5. What I could not finish: the cited Stacks TeX files are absent from this checkout, so I could not inspect their source lines directly. The theorem route and hypotheses were checked against the existing DAG statements and the blueprint route.

## Review by F1

I read the item node, unit `sk-thm-picard-duality`, chapter `sec-picard-framework`, the blueprint ancestor `thm-sc-p1-duality`, and the related existing nodes `def-pur-derived-internal-hom`, `def-weil-abstract-derived-category`, `def-pc-ext`, and `lem-weil-pbc-ext-via-injective-resolution`. The item keeps its original commutative-ring, module, and `n\\ge0` hypotheses. The new bridge node introduces its own ring, modules, and injective resolution and states only the one-point Hom-complex specialization.

Step 1 uses the derived internal-Hom definition, the injective-resolution definition, and the bridge statement; each cited statement explicitly supplies the construction used. Step 2 uses the derived-category cohomology definition and the bridge's explicit cohomology identification; taking cohomology is elementary once those statements are in place. Step 3 uses the existing injective-resolution Ext computation and the Ext definition; the former states the canonical isomorphism with Hom-complex cohomology and the latter states `Ext^i` as the shifted derived-category Hom. The non-elementary facts are all cited, and `citations.json` quotes verbatim text from each cited statement.

For edge cases, I checked `n=0`, where the Hom complex gives `Hom_R(M,N)`, and `M=R`, where higher Ext vanishes for an injective resolution of `N` when expected from the standard calculation. The bridge node was searched by concept and likely names in the DAG, blueprint, Lean source, and Mathlib; LeanSearch, Loogle, and Mathlib grep found no ringed-site RHom specialization. I corrected the initial plain-text arrows and differential notation to TeX and added the missing bridge dependency. No Lean declaration with the item tag or exact statement exists.
