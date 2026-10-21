# Stage-1 delivery: lem-weil-pbc-exact-adjoint-tower-models

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-exact-adjoint-tower-models.json`: item, statement unchanged, split into twelve proof steps. No new nodes and no new Mathlib leaves.
- `citations.json`: 28 entries, one for each node citation of each proof step, with verbatim substrings of the live statements.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `prepare.py` is sandbox-only preparation, not a DAG delivery file.

The item retains its inherited source, created metadata, statement, blueprint provenance, and prior Mathlib searches. I added this worker's actual searches and one product-definition statement dependency. I did not modify any existing dependency node, unit, chapter, Lean source, or repository file.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint id and by tower/K-injective/Roos terminology. The evaluation theorem `CategoryTheory.tower_evaluation_isKInjective` proves one ingredient, not this item. Existing Roos and derived-functor declarations likewise do not jointly state its clauses. No complete attachment was found, and a declaration containing sorry would not qualify.

## WANTED

None. All source passages used are present in `literature/stacks-project/`.

## Findings and corrections

The seeded item had no proof. Its mathematical statement survives unchanged. Its source, Stacks 0A07 (`sites-cohomology.tex`, `lemma-Rf-commutes-with-Rlim`), proves a ringed-topos assertion; the arbitrary exact-adjoint formulation and its sign/unit refinement are an agent extraction, not a quotation of that theorem. `proof_origin.by` is therefore `agent`. I followed the first proof's tower and derived-composition argument, and the current blueprint's product/Roos sentence, without importing its inappropriate suggestion that levelwise injectivity alone resolves a tower.

I avoided two scope errors: `lem-pur-ringed-site-grothendieck-abelian` assumes commutative rings, so I used the existing arbitrary-ring result and the arbitrary-ring small-diagram result instead. Also, despite its ringed-space title, `lem-pc-ringed-space-product-kinjective` has a statement for **every abelian category**; it supplies the general product fact directly. I did not make another node for it or assume exact products to compute derived products.

The negative-difference mapping fibre in the normalized comparison is not silently identified with the positive-difference strict Roos cone. Step 11 writes its differential and the involution on the shifted target coordinate, checks the chain equation, and proves the universal-unit identity by cancellation. Step 12 spells out all three triangle maps and the transported last map. These calculations are required by the item, rather than new lemmas restating its clauses.

The existing normalization node has a malformed old `blueprint.from` string, and its proof is shorter than this item's needs. I do not edit it. I use exactly its stated natural isomorphism and kernel-inclusion identity, subject to all its hypotheses. Its coordinate phrase “zero second coordinate” refers to its native mapping-cocone order; after ordering as shifted target, source, the inclusion is `(0,lambda)`. I checked its source Lean `ExactProductsRoosComparison.lean` through `comparisonApp_f`, where the comparison is built from the ordinary inclusion and zero homotopy. This is a convention check, not an attachment or a reliance on an unstated fact from that proof.

## Unfinished work

None at this splitting level. Every mathematical dependency used below is an existing node. Stage 2 and Stage 3 are outside this delivery. No compiler or Lake command was run.

## Blueprint and duplicate searches

I read the item’s chapter `sec-proper-base-change` and unit `sk-thm-properbasechange`, the current `main-20261015` proof of `prop-weil-pbc-direct-image-limits`, and the source proof at Stacks 0A07. The item is below the product/Roos comparison of that blueprint node, not the unit's key statement; there is no unit record to update. `blueprint_refs.py ancestor` gives `prop-weil-pbc-direct-image-limits`. Searches over the whole DAG and imported blueprint included K-injective, K-injective tower, simultaneous, derived product, and right adjoint, plus 0BK6 and the specific existing node ids. No blueprint node states this whole package in another form; `same_as` remains empty.

## Not duplicates

No new nodes were created, so there are no new/existing pairs. The smaller statements I needed were already present and are cited directly.

## Mathlib searches

The five new searches are exactly those in `searches.jsonl`: LeanFinder with two different semantic descriptions, Loogle with `CategoryTheory.Adjunction, CochainComplex.IsKInjective`, grep with `KInjective|[Rr]oos`, and LeanSearch with the simultaneous-model/unit question. All services answered; none was recorded as unavailable or as an invented empty result. I read the returned types: the first LeanFinder search returned abstract derived-adjunction and exact-functor localization APIs; the second returned bounded-below injective and degreewise-factorization declarations. Neither yields unbounded tower K-injectivity plus the normalized Roos assertion in one line. The grep hits in Mathlib's two KInjective files give the definition, homotopy API and localized Hom bijection. The LeanSearch hits include the abstract unit and right-adjoint-limit facts. These supply ingredients already represented by DAG nodes, not a leaf for this item. The item's inherited NC searches remain attributed by its retained metadata and were not fabricated or repeated.

## Review by NI

I read delivery-errors B through E in full and checked their requirements against the actual node statements and source passages, rather than only the dependency ids. No imported statement was disputed. The statement introduces the two sites, rings, coefficient categories, functors, exactness, universe and all complexes. I checked that the arbitrary-ring hypotheses survive every application, and that exact products are first used in step 10. No SGA source is used.

For step 1, I read the arbitrary-ring assertions in `lem-weil-pbc-ring-sheaves-grothendieck` and `lem-weil-pbc-small-module-diagrams-grothendieck`. The latter allows every small index category in the same universe, so the tower index is allowed. I read Stacks 079P (`injectives.tex`, `theorem-K-injective-embedding-grothendieck`): it explicitly includes injective terms, as does `lem-pur-kinjective-degreewise-existence`. This avoids treating a bare K-injective resolution as automatically termwise injective. This last generic theorem is declared as a tool from another unit.

For step 2, I read the module-sheaf definition and product universal property. The sectionwise construction proves existence and the sheaf property: compatibility and gluing are both checked componentwise. It makes no inference about exactness from sectionwise limits. The entire step is a construction from the cited definitions, so is elementary.

For step 3, I read the levelwise short-exactness statement of `lem-weil-tower-category-levelwise-abelian`, the full exact-adjoint K-injectivity statement, and the injective-object preservation statement. Their source arguments are Stacks 08BJ (`derived.tex`, `lemma-adjoint-preserve-K-injectives`) and 015Z (`homology.tex`, `lemma-adjoint-preserve-injectives`). The pointwise adjunction is written out, and its left adjoint is exact because the short exact sequences really are levelwise. The object-preservation theorem gives injectivity of the **towers** J^r, not merely their evaluations.

For step 4, the evaluation node says precisely that it preserves K-injective complexes of inverse systems, with no product-exactness or boundedness hypothesis. I then construct the constant-tower adjunction by compatible families, verify its left adjoint exact by the levelwise node, and apply the same 08BJ criterion to the ordinary limit. This proves the limit K-injectivity rather than assuming that limits of K-injectives always have it.

For step 5, I read `lem-pc-ringed-space-product-kinjective` and Stacks 0BK6 (`derived.tex`, `lemma-product-K-injective`). Both explicitly state K-injectivity of the termwise product and that it represents the product in the derived category, assuming just the existence of the degreewise products. The hypotheses from step 2 and the evaluated K-injectives from step 4 suffice. This generic product theorem is declared as a tool from another unit. Applying the existing exact-adjoint theorem to P_I gives the additional G(P_I) clause.

For step 6, I read the exact formulation and universal natural-transformation property in `lem-weil-pbc-kinjective-total-derived`, as well as Stacks 070K and 070Y (`lemma-enough-K-injectives-implies`, `lemma-K-injective-defined`). Its input functors are on homotopy categories, not assumed exact on the abelian categories: additive application preserves the actual finite matrices for cones and shifts, which explains the required triangulated exactness. Both tower categories and both module categories have the resolutions required by the theorem. Thus I can apply the universal units successively to I, J and L_I. This is precisely why all four derived objects in the statement are computed by the listed representatives.

For step 7, the right-adjoint limit node allows any small indexing category, not just finite products. I read Stacks 0038 (`categories.tex`, `lemma-adjoint-exact`), part (2). I checked the product and tower cones separately; the differential and strict naturality equations follow by their jointly detecting projections. No unsupported exactness of G is used.

For step 8, I used the actual natural units of the total-derived node, the derived-product conclusion of the product node, the specified components of the shift from `def-weil-tower-transition-endomorphism`, and additivity as defined in `def-weil-pbc-additive-functor`. I checked the n-th component of both shift composites, including the n+1 index; the subtraction then has the correct order and sign. This proves the compatibility that the blueprint leaves implicit.

For step 9, I read the full Hom bijection and homotopy-equivalence consequence in `lem-weil-pbc-kinjective-hom-derived` and Stacks 070I. Its source and target categories can be tower categories, so the derived morphisms here really admit strict chain representatives modulo homotopy. Additive functors, products and limits respect those homotopies by the displayed differential equation. This supplies the claimed localized naturality; it does not mistake a merely levelwise homotopy for a tower homotopy.

For step 10, I read `lem-weil-derived-limit-roos-complex` completely: it applies to arbitrary abelian categories with exact countable products and enough injectives, and its argument node is K-injective as a **tower**. Both I and J meet that condition. Its statement has the exact differential and kernel inclusion of this item, which I compared against `def-weil-strict-roos-model`. I read Stacks 0941 (`sites-cohomology.tex`, `lemma-derived-limit-is-ok`) for the underlying injective-tower sequence, and the 070M discussion for the split-model origin of the existing general Roos lemma. I invoke its stated conclusion, not a construction hidden inside its proof.

For step 11, I read the whole statement of `lem-weil-pbc-exact-products-roos-comparison`. Its comparison is natural and normalized on the ordinary-limit kernel inclusion; it requires Grothendieck towers, exact products and a comparison invertible on K-injectives. All three are explicitly verified before applying it. The sign calculation proves that its kernel inclusion maps to this item's j_T, so the resulting unit equality follows by the displayed cancellation. I am not using just an abstract isomorphism of the two Roos objects.

For step 12, I read the cone convention in `def-weil-abstract-derived-category` and the rotation axiom in `def-weil-triangulated-category`. With cone triangle `(u,i,-p)`, inverse rotation gives `(p[-1],u,i)` with the signs as stated. I computed both transported maps, including the inverse shifted j in the last arrow. This is an elementary application of the definition and the unit equality already proved, not an uncited theorem about derived inverse limits.

I tested the zero ring/zero complex and zero functor cases, the identity adjunction, constant identity-transition towers, and zero-transition towers. For a zero-transition tower u=1, the fibre is contractible and its limit is zero, agreeing with j and the signs. For a constant identity tower, the ordinary-limit inclusion is the diagonal with zero shifted coordinate; the sign involution fixes it, so the unit normalization is unchanged. None of the projection calculations assumes commutative coefficients, surjective transitions, boundedness, or exact products before the conditional clause. All steps are under 2000 characters and contain no hidden long subsidiary lemma. I checked the dependency closure for return edges to the item; none occurs. The mathematical proof is complete at one splitting level with zero new nodes, and citations.json covers every cited node with a literal statement quote.
