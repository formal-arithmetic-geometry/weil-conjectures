1. files written

- `dag/nodes/sec-curve-estimates/lem-sc-etale-qcoherent-descent.json`: item, statement, split proof, Stacks/Mathlib searches; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-etale-qcoherent-descent-fpqc-sections.json`: statement, unsplit classical input; no Mathlib match.

2. attachments

None.

3. WANTED

None. The cited Stacks source is listed as obtained in `literature/LIST.md`; I checked the current online text of Tags 03DR and 03DT because this checkout does not contain the fetched documents.

4. what was wrong in the node, blueprint, or brief

The imported node had no proof steps and treated Tag 03DR as an undischarged input. Its statement also omitted explicit statement dependencies for schemes, quasi-coherent modules, pullback, and presheaf functoriality. I added those dependencies and split the argument at the fpqc descent input. No statement was weakened. The source's proof uses Proposition 35.5.2 (Tag 023T), so the new fpqc-sections node is deliberately unsplit and records that classical input rather than pretending its affine descent proof is elementary. The generic fpqc descent node `lem-pc-fpqc-descent` is declared as a tool use because this unit's route has no replacement for effective descent of quasi-coherent modules.

5. what I could not finish, and why

No Lean was written or compiled, as required for stage 1. The new fpqc-sections node remains in the queue for a later worker.

## Review by J1

I read the item node, its blueprint proof text, the unit `sk-prop-h2`, and Stacks Section 35.8. The online Tag 03DR page identifies the exact presheaf `(f:T→S) ↦ Γ(T,f^*F)` and Lemma 35.8.1 (Tag 03DT) says it satisfies the sheaf condition for etale coverings; its proof first observes that etale coverings are fpqc and then applies quasi-coherent descent, Proposition 35.5.2 (Tag 023T). The item statement therefore agrees with the source for the hypotheses scheme and quasi-coherent module and for the conclusion on the small etale site.

The first item step cites `def-weil-pbc-etale-site` for what a covering family is and `lem-weil-pbc-fpqc-finer-than-etale` for the needed flatness and finite affine refinement hypotheses; this is the exact etale-to-fpqc implication in Stacks Tag 022C. The second step cites the new node, whose statement is the section existence and uniqueness conclusion of Tag 03DT for an arbitrary fpqc covering and explicitly introduces `S`, `T`, `f`, `F`, `g_i`, and the compatibility condition. The third step cites the existing presheaf-functoriality node and the small-etale-site definition; it checks that the compatible-section equalizer is exactly the sheaf condition for the stated presheaf. Only this final identification is marked elementary.

For the new node I checked the complete statement against Tag 03DT's proof: the pullback module is `f^*F`, the cover is of `T`, the sections live on `T_i`, and the equalities are on `T_i ×_T T_j`; the uniqueness is part of effective descent. I searched the DAG and blueprint for this statement and found no duplicate. I searched LeanSearch, Loogle, and Mathlib/source grep for the exact section-descent assertion. The closest declarations are `Scheme.Modules.isSheaf_etaleHom` and `isSheaf_etaleStructurePresheaf_aux`; neither states the general section presheaf, so I recorded no Mathlib match. Small edge cases checked were a singleton covering (the conclusion reduces to the identity restriction) and the empty compatible family, which cannot occur for an fpqc cover of a nonempty target; no extra hypothesis was inserted.

I corrected the original empty proof, added all notions used in the statement as dependencies, filled the blueprint references, and retained the classical descent theorem as an explicit unsplit node rather than hiding its proof in an elementary step.
