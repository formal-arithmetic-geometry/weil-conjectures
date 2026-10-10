Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-ringed-space-restrict-injective-resolution.json`: statement node, split with no new nodes; Mathlib searches found no matching theorem.
- `citations.json`: verbatim citations for every node used by every proof step.
- `report.md`.

Attachments:

- `lem-sc-derived-open-restriction-adjunction-exact` supplies the exact restriction functor and exact extension-by-zero left adjoint used here.
- `lem-sp-right-adjoint-preserves-injectives` supplies preservation of injectives by the right adjoint restriction.

WANTED: `literature/stacks-project/cohomology.tex`, Lemma 01E1 (lemma-cohomology-of-open), part (1) and proof, because the imported literature checkout contains only citation metadata and not the TeX source.

The original node had no proof. No statement or hypothesis was changed. No new child node was created: the apparent extension-by-zero lemma is already present as `lem-sc-derived-open-restriction-adjunction-exact`; creating a ringed-space duplicate would violate the DAG duplicate check. The proof now separates exactness of the restricted augmented complex, injectivity of each restricted term, and the final injective-resolution conclusion.

Nothing remains unfinished in the split. The Mathlib search service `leansearch` was unavailable for both the item and the existing-adjunction formulation; LeanFinder, Loogle, and Mathlib grep were run and found no matching ringed-space theorem. The recorded node retains the available searches and no Mathlib match.

## Review by E1

I read the target node, its blueprint ancestor `lem-sc-pic-proper-ntorsion`, the Mayer–Vietoris parent `lem-sc-mayer-vietoris-ringed-space`, and the existing source-backed node `lem-sc-derived-open-restriction-adjunction-exact`. That existing statement explicitly gives both facts needed from the open immersion: restriction is exact, and it has an exact left adjoint extension by zero. I also read `lem-sp-right-adjoint-preserves-injectives`; its statement applies to an exact functor with a right adjoint and says the right adjoint sends injectives to injectives, matching the orientation `j_! ⊣ j^{-1}`. Finally I checked the definition node `def-sp-injective-resolutions`, which defines a resolution as a bounded-below complex of injectives with cohomology concentrated in degree zero.

Step 1 uses the exactness clause of the open-restriction node and the resolution definition, so termwise restriction preserves the augmented exact complex. Step 2 uses the same node for the adjunction and exactness of `j_!`, then applies the generic right-adjoint lemma to each injective term; the abelian-module and injectivity hypotheses are those stated in the cited definitions. Step 3 is the direct conclusion of the injective-resolution definition from exactness and termwise injectivity. I checked the edge cases of an empty open (the zero restricted complex) and a singleton open (identity restriction), and checked that every citation quote in `citations.json` is verbatim from the cited node statement.

## Second reading by E1

- Item statement: checked against Stacks Cohomology Lemma 01E1(1) as identified in the node; hypotheses $X$, open $U$, $\\mathcal O_X$-module $F$, and an injective resolution are retained, with no added conclusion beyond restriction being an injective resolution.
- Node statement: checked as a statement-only split node; all notions cite definition nodes, TeX is escaped once, and the source tag/label is recorded. Empty-open and identity-open cases are valid.
- Step 1: checked against `lem-sc-derived-open-restriction-adjunction-exact` and `def-sp-injective-resolutions`; exactness of restriction is exactly the cited hypothesis, so applying it termwise to the augmented exact complex is valid.
- Step 2: checked the orientation $j_!\\dashv j^{-1}$ and exactness of $j_!$ against the cited adjunction node, then applied `lem-sp-right-adjoint-preserves-injectives` with the exact left adjoint and right adjoint restriction; the cited injectivity definition supplies the object class.
- Step 3: checked the restricted category's abelian and enough-injectives hypotheses against `lem-sc-ringed-space-module-sheaves-enough-injectives` instantiated at $U$, then applied `def-sp-injective-resolutions` to the exact complex with injective terms.
- Existing-node audit: searched the DAG for restriction/extension-by-zero and right-adjoint preservation facts; the generic adjunction node and generic injective-preservation node already state the needed facts, so no child node was created.
- Source audit: the repository contains citation metadata but not `literature/stacks-project/cohomology.tex`; the report retains the requested source location and makes no claim that unavailable TeX was inspected.
- Changes: added the enough-injectives citation and dependency to Step 3, added its verbatim quotation to `citations.json`, and appended this audit section.
