## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-etale-normal-generic-components.json`: statement node, split into eight proof steps; no Mathlib match for the complete statement.
- `citations.json`: 21 verbatim statement quotations, one for each cited node in each step.
- No new DAG nodes and no new Mathlib leaves. `searches.jsonl` retains the actual search command records.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint tag and normal/finite-etale/generic-component concepts. No project declaration states the entire item under these hypotheses. `Scheme.isIntegral_and_isIntegrallyClosed_stalk_of_etale` in `NormalizationCover.lean` proves a connected-source normality assertion, not the component/generic-field/normalization package. `Scheme.normalization_comp_of_finite_etale` there assumes a finite-type scheme over a field, which is stronger than the present Noetherian hypothesis, and does not provide all clauses. Neither is an attachment for this item.

## WANTED

None. The Stacks sources needed here are present locally.

## Corrections and scope

The item's statement is unchanged. Its proof was empty. I filled it using Stacks 0BQL and 02GL, explicitly supplying restriction to components, surjectivity, the generic-field calculation and the affine normalization equality. No unit or chapter was edited. Its existing `blueprint.from.node = null` and inherited ancestry are retained; `tools/blueprint_refs.py ancestor` confirms this null ancestor. The existing precise `from.place` is retained and `same_as` remains empty after whole-blueprint searches. The item serves the inherited alteration prerequisite in `det-thm-sf-ctf-stability-direct-images`, via `lem-sfb-tame-radical-curve-normalization`, by selecting the actual generic field factors of the radical algebra.

The generic scheme/algebra statements outside this unit are listed in `split_report.tool_uses` where required. In particular, normal-component decomposition, integral function fields, etale-fibre classification and normal-section decomposition are tools for this prerequisite; they do not replace any constructibility-unit step.

While searching I noticed an unrelated statement error, which I did not use or edit: `lem-weil-pbc-flat-generalizations-lift` says that specializations lift along flat maps. For the flat map from the generic point `Spec Frac(A)` into `Spec A`, with A a DVR, the closed point specializes from the generic point but has no preimage. Stacks 03HV states that *generalizations* lift. This delivery instead uses the correctly stated etale open-map node and finite closed-map node.

## Not duplicates

No new nodes. Whole-DAG statement searches and `tools/blueprint_refs.py search` for `normal integral`, `étale over`, `normal sections`, `normalization finite`, `finite etale cover`, and `generic field` found the existing component and fibre tools. In particular I reuse `lem-fin-etale-normal-components` rather than creating a decomposition lemma, and `lem-sbc-normal-sections-finite-product` rather than creating a normal affine-section lemma. Neither of those states the whole item, so neither is `same_as` for it.

## Review by Q48

I read `pione.tex`, Tag 0BQL, `lemma-finite-etale-covering-normal-unramified`, including both proof paragraphs. Its first paragraph supplies the normal component route and its second identifies the connected cover with normalization in its function field. I also read `morphisms.tex`, Tag 02GL, `lemma-etale-over-field`, including the precise finite-separable residue-field conclusion and its proof. There are no new nodes needing separate source review.

For step 1 I checked the definitions of finite morphism and finite type: a finite module's generators generate its algebra, and a finite morphism has an affine inverse image of each affine chart, so it is quasi-compact. This is exactly what the cited 01T6 node needs to conclude that Y is Noetherian; no finite-type-over-a-field assumption is inserted. I read 01T6 in `morphisms.tex`.

For step 2 I opened `lem-fin-etale-normal-components`: its statement requires the source W to be Noetherian and the target to be normal integral, and concludes a finite clopen decomposition into normal integral schemes. Step 1 supplies the source hypothesis; the item supplies the target hypothesis. I read its current blueprint proof in `main-20261015/.../lem-fin-etale-normal-components.proof.md` and Properties 0357. The integral-scheme definition supplies nonemptiness, including the reason to use no components for the empty cover.

For step 3 the clopen inclusion is shown to be a closed immersion directly: extend every section by zero on the complementary open. The cited closed-immersion definition says precisely homeomorphism onto a closed subset plus surjectivity of the structure-sheaf map. I read the statements of the closed-immersion-finite, finite-composition and etale-composition-cancellation nodes, and their Morphisms sources 035C, 01WK, 02GP and 02GN. They apply to the actual inclusion and the given p. No theorem about arbitrary closed subsets factoring as immersions is assumed.

For step 4 I read the finite closed-map/fibre node and the etale open-map node and checked their exact conclusions. They apply to p_i from step 3. The image is nonempty clopen, and irreducibility of X excludes a nonempty complement. I read Morphisms 01WN and 03WT. This proves surjectivity without relying on the reversed specialization statement noted above.

For step 5 I opened every cited statement: finite morphisms give the finite affine chart B; the integral-scheme definition gives its domain property; `lem-sc-integral-function-field-affine-fraction` supplies the two actual germ embeddings and the fraction fields; `lem-weil-pbc-fibre-product-affine-spectra` supplies the tensor algebra with its projection maps; and `lem-weil-pbc-etale-fibre-discrete-separable-points` supplies spectra of finite separable extensions for the fibre over the generic point. I read the corresponding sources 01RV, 01I4, 01JQ and 02GL. Surjectivity supplies a prime contracting to zero, so A embeds in B. The written tensor/localization maps show the generic fibre is a nonzero domain. An irreducible spectrum cannot be a disjoint union of two nonempty open field spectra. Its unique field is therefore the fraction field of B, with equality through the specified germ embedding. No algebraic-closure or perfectness hypothesis is used.

For step 6 I read `lem-sbc-normal-sections-finite-product`: it concerns sections over a quasi-compact open in a locally Noetherian scheme with normal-domain stalks. Y_i has these hypotheses from steps 1 and 2, and its inverse image of V is affine and hence quasi-compact. Its section ring B is a nonzero domain, so the finite product in that cited statement has exactly one factor, by the explicit idempotent argument. This is a few-line specialization, not a new node. I read Properties 0358 and its proof, and Algebra 00GK (`lemma-finite-is-integral`). The latter node gives B integral over A. The same monic equation makes any element of F_i integral over A integral over B. This proves both inclusions of the integral closure, rather than invoking a definition for a theorem.

For step 7 I read `def-fin-normalization-extension` in full. Unlike a mere name for normalization, its statement gives the affine integral-closure construction and explicitly states localization compatibility. The chart equalities of step 6 are equalities inside the fixed F_i. On every principal open both maps are the same localization map, so they agree on affine overlaps and glue. This step is marked elementary, with that definition cited; it hides no independent normalization comparison lemma.

For step 8 I opened `lem-sc-etale-fibre-product-base-change-coproduct`. Its statement gives the isomorphism and both projection compatibilities, which are exactly the compatibilities used here. I read the cited Schemes gluing and affine fibre-product material. Primitive idempotents of a finite product of fields are proved to be the coordinate idempotents directly. Thus repeated isomorphic fields do not create a false uniqueness claim about isomorphism types.

I checked B–E of `coord/delivery-errors.md`: there are no statement-only helper violations, duplicated or clause-restating nodes, invented Mathlib leaves, or uncited geometric black boxes. Every proof citation has a verbatim quotation in `citations.json`. The new search records are exactly the executed leanfinder/loogle/grep/leansearch queries. I read the normalization coproduct declaration in Mathlib and the field-algebra search hits: neither is the complete item. The second semantic phrasing also gives only the field-algebra classification, not the scheme theorem. All eight steps are below 2000 characters, so no long step conceals another lemma.

Small cases checked: empty cover (empty I and zero generic algebra); the identity cover; two copies of X (two coordinate factors even though their fields are isomorphic); a finite separable field extension over a field base (one component and its field spectrum); characteristic p over an imperfect field (02GL still gives separability); and a higher-dimensional normal Noetherian base. The argument does not assume excellence, geometric connectedness, a chosen rational point, or a finite-type field base. The proposed unrestricted specialization-lifting shortcut fails already over a DVR and was excluded.

## Unfinished work

None in the one-level split. The required dry run and delivery validate this sandbox; no Lean was written and no compiler, Lake or build command was run.
