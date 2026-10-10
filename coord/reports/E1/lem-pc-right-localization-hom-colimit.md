1. Files written:
- `dag/nodes/sec-picard-framework/lem-pc-right-localization-hom-colimit.json`: split statement node.
- `dag/nodes/sec-picard-framework/lem-pc-right-fraction-representation.json`: Mathlib leaf, `CategoryTheory.Localization.exists_rightFraction`, `Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:966`.
- `dag/nodes/sec-picard-framework/lem-pc-right-fraction-common-refinement.json`: Mathlib leaf, `CategoryTheory.MorphismProperty.RightFraction.map_eq_iff`, `Mathlib/CategoryTheory/Localization/CalculusOfFractions.lean:973`.

2. Attachments: none.

3. WANTED: `literature/stacks-project/categories.tex`, Tags 05Q4, 04VI, and 04VJ, for the exact source TeX of the right-localization formula and fraction lemmas. I read the corresponding online Stacks pages; the local literature checkout contains only citation metadata, so the item proof is marked `by: agent`.

4. The imported item statement omitted that the indexing category is `(S/M)^{opp}` and did not state its commuting-triangle morphisms; I repaired the statement to match Remark 05Q4. The proof now gives the canonical map, checks compatibility, proves surjectivity from right-fraction representation, and proves injectivity from common refinement. The right-fraction and common-refinement facts were searched in the whole DAG and blueprint; no existing node stated either fact. The Mathlib searches found exact declarations for both inputs, but no full colimit theorem.

5. I could not compile Lean because stage 1 forbids builds and no Lean file is being written. The mathematical edge cases checked were the identity-only multiplicative system and two representatives with identical denominators.

## Review by E1

I read the imported item and its ancestor route in `lem-sc-finite-duality`, and checked the online Stacks sources: Remark 05Q4 gives the category `S/M`, its cofilteredness, and the colimit formula; Lemma 04VI gives right-fraction representatives; Lemma 04VJ gives the common-refinement equality criterion. The item statement now includes the right multiplicative-system hypothesis, the opposite indexing category, the commuting-triangle index morphisms, and the explicit canonical map. Step 1 is elementary compatibility of that map with index morphisms. Step 2 uses only the exact representation statement of `lem-pc-right-fraction-representation`, quoted verbatim in `citations.json`; Step 3 uses only the exact common-refinement statement of `lem-pc-right-fraction-common-refinement`, also quoted verbatim; Step 4 is the elementary conclusion and identity-system sanity check. Both new nodes are statement-only Mathlib leaves, with their declarations and source lines recorded. I ran the required `msearch.py` LeanFinder, Loogle, grep, and LeanSearch searches for the item and each new node; LeanSearch was unavailable and is recorded as such. I also checked blueprint references and DAG keywords before creating either node; no duplicate or blueprint statement was found.

## Not duplicates

`lem-pc-right-fraction-representation` vs `lem-pc-right-localization-hom-colimit`: the new leaf states only existence of a single right-fraction representative, while the item states the bijection with the entire filtered colimit.
`lem-pc-right-fraction-common-refinement` vs `lem-pc-right-localization-hom-colimit`: the new leaf states only equality of two right-fraction representatives via a common refinement, while the item states the full colimit bijection.

## Second reading by E1

- Item statement: checked against Categories Remark 05Q4 (local `categories.tex`, label `remark-right-localization-morphisms-colimit`); the right multiplicative system, `(S/M)^{opp}` indexing category, commuting triangles, and canonical fraction map agree hypothesis by hypothesis.
- Step 1: checked the transition-map orientation and composition types against the diagram and formula in Remark 05Q4; corrected the denominator in the compatibility equation so both sides are well typed.
- Step 2: checked against Lemma 04VI / `lemma-morphisms-right-localization` and the exact statement of `lem-pc-right-fraction-representation`; the cited leaf supplies precisely the right-fraction representative.
- Step 3: checked against Lemma 04VJ / `lemma-equality-morphisms-right-localization` and the exact statement of `lem-pc-right-fraction-common-refinement`; the common-refinement equalities are exactly the colimit relation.
- Step 4: checked the bijection conclusion and identity-only multiplicative-system case directly; both are correct.
- `lem-pc-right-fraction-representation`: statement-only, self-contained with definition dependencies, source and Mathlib declaration/lines recorded; tested on identity localization and found no existing DAG duplicate.
- `lem-pc-right-fraction-common-refinement`: statement-only, self-contained with definition dependencies, source and Mathlib declaration/lines recorded; tested on identical denominators and found no existing DAG duplicate.

Changes made: repaired Step 1's typed compatibility equation (`Q'(f ∘ a) ∘ Q'(t)⁻¹ = Q'(f) ∘ Q'(t')⁻¹`) and recorded the source/node checks above; no node was removed.
