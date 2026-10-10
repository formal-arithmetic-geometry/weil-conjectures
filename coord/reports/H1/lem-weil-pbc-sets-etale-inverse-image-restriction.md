1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-etale-inverse-image-restriction.json`: split statement; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-adjoint-continuous-restriction-adjunction.json`: statement-only dependency; no Mathlib match.
- `citations.json`: verbatim statement excerpts for every proof citation.

2. Attachments: none.

3. WANTED: none.

4. The imported item had only a grep search and no proof. I retained its statement and filled the missing sets-valued proof. The abelian restriction-adjunction node was not used because its statement is restricted to abelian sheaves; I created the sets-valued statement-only node instead. The source route is Stacks Tags 03S2 and 00XZ, with localization and covering details from Tags 00WW, 00XX, 00XY, 021F, 021H, and 021I.

5. I could not compile Lean by stage-1 policy; this delivery contains only DAG JSON and the report.

## Review by H1

I read the item source in `literature/stacks-project/etale-cohomology.tex` (Tag 03S2) and `sites.tex` (Tag 00XZ), and read the existing statements of every cited node. Step 1 uses the localization functor and its counit from `lem-weil-pbc-etale-localization-functor-adjoint`, plus the objectwise direct-image formula; those statements explicitly provide the functors and projection. Step 2 checks the sheaf equalizer after restriction and after base change, using the site definition, fibre-product definition, the covering-base-change lemma, and finite-limit preservation; each cited statement supplies the corresponding covering or fibre-product fact. Step 3 uses the new sets-valued adjunction node, whose hypotheses and unit formula are stated self-containedly, together with the localization counit and direct-image definition. Step 4 uses the existing sets inverse-image construction, which explicitly says it is left adjoint to direct image, and the new node's uniqueness clause to obtain the natural isomorphism. Step 5 is the objectwise unit calculation and terminal-object identification, using only the direct-image and fibre-product statements, so it is marked elementary.

For the new node I searched the DAG and found only the abelian analogue; no sets-valued restriction-adjunction node existed. I searched Mathlib by natural-language LeanSearch, semantic LeanFinder, and source grep for sheaf pullback/restriction and found only generic sheaf-pullback/over-site declarations, so the node is unsplit. I checked the edge cases of the terminal object and empty covering families in the site equalizer formulation; no additional hypotheses are used. The item's blueprint `from.place`, `same_as`, proof dependencies, and split report were filled, and every citation quote was copied from the cited statement.
