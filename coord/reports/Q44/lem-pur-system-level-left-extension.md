# Stage-1 report: lem-pur-system-level-left-extension

1. Files written:

   - `dag/nodes/sec-smooth-purity/lem-pur-system-level-left-extension.json` — existing item statement preserved; its reopened long step 6 is now five proof steps, all below 2000 characters.
   - `dag/nodes/sec-smooth-purity/lem-pur-system-section-cone.json` — new statement-only lemma; Mathlib searches found no match.
   - `dag/nodes/sec-smooth-purity/lem-pur-system-section-suspension.json` — new statement-only lemma; Mathlib searches found no match.
   - `citations.json` — 31 verbatim statement quotations for every cited node in every proof step.

2. Attachments: none. I searched the read-only slopmaster2 source for the item id, semilinear systems, evaluation adjoints, cones and derived left extensions. The hits are generic ordinary category-theory or exact-adjunction declarations and do not state this varying-ring unbounded derived theorem. No declaration with this item’s statement and a finished proof was found.

3. WANTED:

   - WANTED: a flat differential graded model reference for module sheaves on arbitrary small ringed sites, for `lem-coef-sheaf-flat-model`.
   - WANTED: an enriched section-rectification reference for `lem-coef-quillen-section-rectification`.
   - WANTED: an enriched derived Quillen/coherent-localization reference for `lem-coef-dg-derived-quillen-calculus`.

4. The imported item was reopened by the human decision of 2026-10-17 because its sixth proof step was 2429 characters and hid several lemmas. I kept the statement, hypotheses, definitions, route, and all other steps unchanged. I split that step into projective-section rectification, the right-Quillen evaluation argument, a cone calculation, a suspension pushout calculation, and the derived-adjunction application. The two middle arguments are new statement-only nodes; their statements introduce the projective section model and all cone objects they use. No statement dispute was found.

## Not duplicates

`lem-pur-system-section-cone` vs `lem-coef-sheaf-flat-model`: the latter states existence and stability of the single-ring module-sheaf model; the new node concerns the componentwise cone inside a varying-ring projective section model.

`lem-pur-system-section-cone` vs `lem-coef-pointed-model-stability`: the latter is the abstract suspension criterion for a model category; the new node supplies the concrete cone cofibration, cokernel, and contraction required for these sections.

`lem-pur-system-section-suspension` vs `lem-coef-pointed-model-stability`: the latter only says that a cofibrant span’s ordinary pushout computes its homotopy pushout and gives a stability criterion; the new node computes this particular pushout as the shift for the semilinear section model.

`lem-pur-system-section-suspension` vs `lem-cbc-grothendieck-coherent-end`: that node concerns homotopy-coherent ends of presheaves on a different Grothendieck construction; it does not state the cone pushout or suspension of coefficient sections.

5. Mathlib search record: for each new node I ran `leanfinder`, `loogle`, `grep`, and `leansearch` through `msearch.py` with the queries recorded in its `mathlib_searches`. Mapping-cone declarations such as `CochainComplex.mappingCone.homotopyToZeroOfId` and `CochainComplex.mappingCone.rotateHomotopyEquiv` were read as generic complex facts; none states either new section-level lemma, so neither node is a Mathlib leaf.

## Review by Q44

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B–E before editing. I read the current item, its chapter and `sk-def-sf-operations` unit metadata, the current main-20261015 `def-weil-exceptional-inverse-image` adic-stage text, and the cited generic foundations. The Zheng Construction 4.1 source remains the prototype for the evaluation extension; it does not itself assert the arbitrary sheaf-ring and subsequence derived statement.

For steps 1–5 and 11–13 I retained the existing proof text and reread every cited node statement. Step 1 uses the ringed-site Grothendieck and module-sheaf-colimit statements exactly for the product-site construction and componentwise exactness. Step 2 uses the K-injective resolution, derived Hom, and derived exact-functor statements for arbitrary-small coproducts and joint detection. Steps 3–4 use only the ordinary module tensor/restriction adjunction while explicitly checking the evaluation and subsequence system maps. Step 5 uses the flat model, tensor exactness, pullback preservation of K-flatness, and derived change of rings to establish the Quillen diagram without assuming flat coefficient maps. Step 11 uses the flat model, section rectification, dg calculus, and derived change of rings for the displayed formulas; step 12 checks the transition and coherent Kan-extension comparison; step 13 checks the index identity and coherent composition. The hypotheses used in each of these citations are present in the item’s statement or in the preceding step.

The replacement step 6 first applies `lem-coef-quillen-section-rectification` and `lem-coef-semilinear-derived-sections`; these statements give the projective section models, componentwise weak equivalences/fibrations, cofibrant evaluations, and the ordinary derived categories. Step 7 verifies the right-Quillen claim from componentwise fibrations and the adjunction in `lem-weil-pbc-ringed-topoi-module-adjunction`; transposing lifting squares is the only extra argument. Step 8 cites the new cone node and the abstract pointed-model criterion. Its statement says exactly that the identity cone map is a cofibration, its cokernel is the shift, and the cone contracts componentwise. Step 9 cites the new suspension node and the abstract criterion; it states exactly that the two-cone pushout is quasi-isomorphic to the shift and that the inverse shift makes suspension an equivalence. Step 10 then applies the existing enhanced dg Quillen calculus to the now-stable models and records the actual evaluation and restriction derived functors, units, counits, and triangle identities.

I checked the small cases used by the new nodes: the zero section, a one-level section, and a constant coefficient system reduce to the ordinary cone calculation; componentwise contractibility is preserved by the section structure maps. The pushout calculation has degreewise coordinates `(y,x_1,x_2)` and projection to the shifted coordinate, with contractible kernel, so it remains a quasi-isomorphism without flatness or boundedness assumptions. I also checked the identity selection `r(i)=i`, where all restriction and left-extension comparisons are identities. Every proof step is below 2000 characters after the repair. The item and both new nodes have no Lean declarations, no SGA citations, no cycles, and all `uses` entries are included in `proof_deps` and quoted verbatim in `citations.json`.

6. Nothing remains unfinished in this stage. No Lean, compiler, Lake, or build command was run, and all writes are confined to the Q44 sandbox.
