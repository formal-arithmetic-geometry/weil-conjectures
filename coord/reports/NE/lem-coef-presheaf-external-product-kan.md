# Stage-1 report: lem-coef-presheaf-external-product-kan

## Files written

- dag/nodes/sec-six-functors/lem-coef-presheaf-external-product-kan.json — item, statement, split in seven steps; no Mathlib match for coherent infinity-category assertion.
- dag/nodes/sec-six-functors/lem-coef-infinity-product-colimit-fubini.json — one new statement-only supporting lemma, unsplit; no Mathlib match. This is Fubini for arbitrary coherent diagrams with values in any suitably cocomplete quasicategory, not an external-product Kan assertion.
- citations.json — exact statement quotations for every step/node pair.
- report.md — this report. Local preparation scripts are sandbox-only helpers, not delivery files.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag, external products of presheaves, product Kan extensions and Fubini. Its matches concern ordinary Kan extensions (including oplax monoidal structure), sheaves and derived external tensor products. None states the item for coherent functors to the coherent nerve of small Kan complexes. No missing own Lean declaration was reported by the item. The upstream master remains reference material only.

## WANTED

WANTED: Chu--Haugseng, Homotopy-coherent algebra via Segal conditions, https://arxiv.org/pdf/2006.08269, Corollary 6.10 and its proof, for the item and the new coherent Fubini lemma. The PDF is not archived under literature/. I read its proof online through a streaming pdftotext read; no literature file was downloaded or modified. The source explicitly uses the product-comma pointwise formula and commutation of products with colimits in each separate variable. The general Fubini statement makes precise the independent-index colimit interchange used in that calculation. Since the source is not archived, proof_origin is agent, with the explicit argument expanded below and in the item.

No Stacks tag states these quasicategorical assertions. Stacks Categories 002M and the ordinary Mathlib Fubini theorem are analogues; neither is cited as if it proved coherent Fubini.

## What was wrong or missing

The item was unsplit and had no proof. Its statement is correct and has been retained verbatim, including arbitrary comma categories, coherent transformations, finite regrouping and the empty family. There was no completed prior split or report: the sandbox contained only marker files and six Fubini search records. I retained all these searches, read their Mathlib hits, and reused them for the unchanged coherent Fubini question. No API failure invalidates them. Fresh logged item searches supplement the item's historical searches.

The ordinary Mathlib hits are close in words but not in objects. I read Mathlib/CategoryTheory/Monoidal/ExternalProduct/KanExtension.lean:30-105, Limits/Fubini.lean:450-536 and 638-669, and AlgebraicTopology/SimplicialNerve.lean:24-32. They use ordinary Category/Functor instances; the last source still lists constructing the quasicategory of spaces as a project. There is no one-line specialization from the ordinary results to this item or the new lemma. All recorded queries correspond to actual msearch.py logs; unavailable services were not treated as absence. The successful curl/stream read resolved the earlier browser 429 without repeating any delivery or mutation.

## Not duplicates

lem-coef-infinity-product-colimit-fubini vs lem-pc-colimit-fubini: the existing Mathlib leaf concerns ordinary categories and the interchange of two ordinary colimits; the new assertion is about coherent colimit cocones in arbitrary quasicategories and all mapping-space/higher compatibility data.

lem-coef-infinity-product-colimit-fubini vs lem-coef-coherent-end-twisted-arrow-formula: the latter gives coherent ends and a Fubini formula for mapping spaces expressed as particular limits; it does not give colimits of arbitrary diagrams in a quasicategory or their composite colimit cocones.

lem-coef-infinity-product-colimit-fubini vs lem-coef-cartesian-grothendieck-colimit-formula: the latter only treats nerves of ordinary Grothendieck constructions and diagrams inverting the specified transport arrows. It does not cover arbitrary indexing quasicategories and arbitrary coherent product diagrams.

lem-coef-infinity-product-colimit-fubini vs lem-coef-derived-space-module-coyoneda: the latter concerns enriched modules and derived coends over small simplicial categories, not arbitrary coherent colimits in a quasicategory.

lem-coef-infinity-product-colimit-fubini vs lem-coef-infinity-sifted-colimit-calculus: the latter compares a diagonal diagram over a common sifted index with a separately cocontinuous bifunctor. The new lemma concerns independent index categories and assumes no siftedness.

lem-coef-infinity-product-colimit-fubini vs lem-coef-presheaf-external-product-kan: the new lemma contains no presheaf Kan extension, product of values, specified Kan unit or functor-composition assertion. The substantive item argument still identifies comma categories, proves separate product preservation using the existing universal-colimit node, handles finite induction, identifies the unit-defined comparison and proves its parameter and composition compatibility.

I searched all dag/nodes for Fubini, iterated colimits, product-colimit and coherent-colimit keywords; blueprint_refs.py searches for Fubini, iterated colimit, colimits commute and external product found no blueprint node stating the new lemma or the item. The ancestor command gives prop-coef-integral-exceptional-adjoint. I read the current main-20261015 ancestor statement/proof, its unit sk-prop-sf-biduality-general and the chapter. The ancestry stays historical and the split realizes the same foundational finite-coefficient adjunction/Day-presheaf route. The item is not the unit's key node, so no unit fields were edited.

## What remains

The supporting Fubini node is deliberately statement-only and queued for later splitting. No part of the item's split is deferred. No Lean has been written, compiled or built, and no shared repository, source checkout or launcher has been modified.

A proof route for the new lemma (report only, not part of its unsplit statement): let Delta_K:C -> Fun(K,C) be the constant-diagram functor. Its left universal arrows are the K-colimit cocones. The existing parametric-universal-arrows theorem assembles them into colim_K and lifts the adjunction to coherent J-diagrams. Currying Fun(J x K,C)=Fun(J,Fun(K,C)) is the simplicial exponential identity. For any z, mapping out of colim_J L is equivalent first to coherent maps L -> Delta_J z and then to coherent maps H -> Delta_(J x K) z. The map is composition with the inner and outer cocones. The existing cocone mapping-space criterion proves it colimiting. The same argument after exchanging J,K gives the other order, including the empty cases; the parameter clause supplies higher simplices. This is the general identification isolated in the new node rather than hidden in a long item step.

## Review by NE

I checked delivery-errors B through E against the actual files and the sources, not just the file format. For the item I read the product-comma proof of Chu--Haugseng Corollary 6.10, and compared the universes and comma-cocone orientation with the full statement of lem-coef-infinity-space-valued-pointwise-lan. For the new node I read the same source's independent-index calculation, the ordinary Mathlib Fubini source as a non-match, and the full existing parametric-universal-arrow and cocone-calculus statements underlying the report's proposed proof. The general coherent lemma is self-contained, genuinely smaller and statement-only. Its definition dependency supplies all of its notions. Its blueprint.from adds exactly this item to the ancestry, and same_as is empty only after the whole-blueprint searches.

Step 1 uses the enhanced-diagram definition for degreewise products/pullbacks and the pointwise-Lan statement for its explicit arrow comma and its full canonical coherent cocone. I checked the variance: v_i=h_i^op and alpha_i:v_i(a_i)->b_i, so in the original category these are arrows b_i->h_i(a_i). Products, endpoint restrictions and functor simplicial sets are coordinatewise in every degree. The input smallness gives small comma shapes; products of these are still small. No finality, nonemptiness or filteredness is assumed.

Step 2 uses exactly the displayed base-change colimit assertion of lem-coef-space-universal-colimits at B=*, A=X. Its comparison has legs id_X x iota_j, so the result is preservation of the specified cocone, not just an equivalence of apices. The fixed-universe small-colimit statement supplies existence even when X or the index is empty. These statements were opened and read; a mere definition of cartesian closure was not substituted for colimit preservation.

Step 3 uses the new Fubini statement for the composite cocone and the two orderings of separate product preservation from step 2. Its additional small-colimit citation checks every existence hypothesis. I checked the leg at (j,k): it is exactly iota_j x iota_k. This is the only new non-elementary comparison used in the product-colimit calculation.

Step 4 is the finite induction on that binary result; I wrote the claim, the zero-factor base and the successor explicitly. It introduces no independent lemma. The zero-factor index is terminal, not empty, and the diagram has value *. A single empty comma factor for a nonempty family produces the empty space on both sides; this is different from the zero-factor family. The elementary step cites the diagram definition and mapping-space criterion to make its base-case cocone check explicit.

Step 5 reads both clauses of the pointwise-Lan statement: its mapping-space adjunction creates c as the mate of the product unit, and its pointwise cocone fixes every leg of c_b. The cone-calculus statement supplies the cocone universal-property test, contractibility of initial-object choices and componentwise equivalence detection. Thus the argument proves equivalence of the requested map and the equation with the specified units; it does not assume that an arbitrary valuewise equivalence preserves them.

Step 6 uses the full parameter formula and its explicitly stated opposite in lem-coef-parametric-universal-arrows, applied to restriction. It supplies a partial left adjoint and maps of diagrams for arbitrary simplicial parameters in a containing universe. The mate is always formed from the product of units; faces/degeneracies restrict these same maps. Transformations of h_i act by the corresponding restriction mate, and both composites transpose to the same product of transformed units. This checks coherent naturality without treating a mere homotopy-category naturality assertion as sufficient.

Step 7 uses the same mapping-space equivalences and their contractible fibers to compare regrouped products and composite Kan extensions. I wrote the composite unit with its restriction whiskering, checked its type, and checked that both external-product paths transpose to its product. The parameter formula makes the uniqueness comparison coherent at every level. For a zero-factor family this reduces to the identity of the terminal presheaf.

I tested the item on a point index, an empty input category, an empty comma at a particular target object, empty spaces, identities, a zero-factor family and a finite family with an empty factor; none needs a nonemptiness assumption. I tested the new lemma on terminal, discrete, empty and nontrivial coherent arrow shapes. The report's adjunction proof works for each, unlike an ordinary-nerve-only argument. All seven steps are shorter than 2000 characters. The non-elementary Fubini comparison was separated rather than hidden in those steps. Every cited statement has a verbatim quote in citations.json, and I checked quote containment locally. A transitive dependency scan of all existing tools found no path back to the item; the new lemma depends only on the diagram definition. All non-definition proof tools are in the same unit, so tool_uses is empty. No SGA source or forbidden alternative route is used.
