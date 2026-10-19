# NJ: lem-zl-extension-by-zero-punctual

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-extension-by-zero-punctual.json`: statement, split into seven steps; no Mathlib match.
- `citations.json`: a verbatim statement quotation for every step/node citation.
- `searches.jsonl`: actual msearch.py searches, including two semantic phrasings and two Loogle queries. Prior searches already present in the imported item were retained; new searches were appended with their actual query strings and results.
- `report.md`: this report. `bhatt-scholze.txt` and `write_split.py` are sandbox reading/preparation aids and are not DAG delivery files.

No new nodes, Mathlib leaves, unit changes or Lean files.

## Attachments

None. I searched the entire project source for the exact blueprint tag, and searched for extension by zero and punctual weights, then read `WeilConjectures/DeligneLaumon/Reduction/FormalSteps.lean` at lines 562–605. The quasi-finite higher-shriek vanishing and punctual/mixed-weight declarations there contain `sorry`. They do not provide an attachment for this item. Closed finite-coefficient extension declarations do not assert this item's rational Weil-sheaf and weight conclusions.

## WANTED

None. The current blueprint, local Stacks sources and Bhatt–Scholze paper suffice. No forbidden SGA source was used.

## Statement and import issues

STATEMENT-DISPUTED: the original wording attributed “its local Frobenius” to an arbitrary geometric point of the open. This is undefined under `def-weil-local-frobenius-trace`, which defines the local operator at closed points of the finite-field scheme (or specified finite-field-valued points). For example, a geometric point above the generic point of the identity open immersion of the affine line has residue field containing the transcendental element t. There is no positive finite residue-field degree d giving the closed-point return used in that definition. In particular t is not fixed by any positive power of finite-field Frobenius. This is a type/domain problem, not a counterexample to extension by zero.

The corrected statement retains the fibre formula for **every** geometric point, and specifies Frobenius equivariance over closed points, exactly as the current blueprint proof (2) does. It also introduces the finite-field/coefficient data, the actual compact-support extension functor and the adic coefficient-fibre convention. The phrase “punctual upper weight bound” is now explicitly the eigenvalue inequality: the cited punctual-weight definition states purity and filtered mixedness, but does not separately define that inequality. No upper bound or purity conclusion has been dropped, and no restriction on the open immersion has been added.

The imported statement dependencies contained no definition of the extension functor or of coefficient fibres. These are now explicit dependencies. I have not identified the rational/common-stage category with discrete non-torsion small-etale sheaves, nor with the separate condensed coefficient construction.

## Route and sources

I read `dag/chapters/sec-deligne-laumon-general.json`, `dag/units/sk-l-dl-general-quasifinite.json`, and the main-20261015 `lem-zl-quasi-finite.proof.md`. This item supplies precisely the open-immersion portion of paragraphs (1) and (2): exactness, unchanged local Frobenius, and zero complementary stalks. It is not the unit key statement, so no realization fields were changed. No alternate route replaces a unit step.

I read Stacks `sites-modules.tex`, Lemma 03DJ (`lemma-extension-by-zero-exact`), Proposition 03S5 (`etale-cohomology-proposition-describe-jshriek`), and the explicit stalk map immediately after its proof. I also read module tensor Lemma 0E8I and derived tensor Lemma 0GL1 (`lemma-j-shriek-and-tensor` in the respective files), and checked the tags against `tags/tags`. For coefficient passage and restrictions I read Bhatt–Scholze Lemmas 6.1.12–6.1.13, Lemma 6.8.2, Proposition 6.8.14 and Remark 6.8.15. The paper's native categories are not silently substituted for the project's categories: the proof invokes the existing comparison nodes for the actual strict completed towers and then the project's rational/common-stage definitions. The expanded argument is correctly marked agent-written, with the current blueprint as its origin.

## Not duplicates

No new nodes were created. I searched the whole DAG by extension-by-zero, exactness, stalks, Frobenius, coefficient-stage and t-structure terminology, and searched the whole blueprint with `blueprint_refs.py search` for “extension by zero”, “punctual”, and “t-exact”. Existing generic nodes already provide every needed non-elementary input. Neither finite-coefficient exactness alone nor its finite stalk formula is recorded as an exact duplicate of the entire rational Weil statement. The nearest blueprint ancestor remains `lem-zl-quasi-finite`, with its precise proof (1)/(2) place retained. `same_as` is empty because no blueprint node found asserts all the clauses of this supporting item.

## Review by NJ

I checked B–E of delivery-errors against the final node and sources. There are no new unsplit nodes, no moved clauses of the item, and no new definitions to conceal an existence or coefficient-category issue. The seven steps carry the argument; the reused nodes are generic tools, not new names for this item's conclusions. Every cited node's statement was opened and read, and `citations.json` copies statements rather than proof-internal constructions. Off-unit statement tools are declared in `split_report.tool_uses`, with reasons; no maintainer-owned tool field is set.

For step 1 I checked the explicit field-extension specialization in the existing Mathlib leaf `lem-pod-separated-finite-type-base-change`, which supplies separated finite-type schemes over k before applying the coefficient results. I checked that finite type over the field gives Noetherian schemes by `lem-weil-pbc-finite-type-over-noetherian`. Applying `lem-weil-pbc-noetherian-open-subscheme-noetherian` to the intersection of the open with an affine target chart gives exactly quasi-compactness of j. `lem-weil-pbc-closed-subset-closed-subscheme` supplies an actual closed complement. I checked the named Stacks labels; an initially inaccurate closed-subscheme tag was corrected to 01J3. The field's only ideals are 0 and the whole field, so its Noetherian hypothesis requires no extra lemma.

For step 2 I checked the statement of `lem-sf-integral-open-reduction-comparison`, including its **specified** map d_j and compatibility with quotient transitions. It is a comparison of the whole realized system, not unrelated maps at individual levels. This is what identifies the total limit in `def-weil-integral-rational-qbar-compact-support` for the compactification (j,id) with the completed-ring module extension. `lem-pur-site-restriction-module-adjunction-exact` applies to arbitrary ringed sites and hence to that completed ring sheaf. Exactness gives the displayed cohomology equation by kernels and images. `lem-sf-integral-compact-support-constructible` gives constructible landing for the same compactification and coefficient tower; it is not inferred from completeness alone.

For step 3 I read both cohomological classes in `def-weil-constructible-standard-tstructure`. Preserving them is justified by choosing a representative in the desired class and applying the integral argument; it does not assume that every rational heart representative is concentrated in degree zero integrally. The compact-support definition gives the finite-field/common-stage action, and clause (1) of `prop-functor-package` supplies the needed compatibility. Their intersection is the heart of `def-weil-constructible-heart`. Thus the output is a sheaf before any exactness test is used.

For step 4 I checked the quasi-compact-open hypothesis and coefficient datum of `lem-cbc-completed-extension-zero-comparison` with R=O_E and I=(uniformizer). It allows arbitrary base change, so applies to j and the closed complement i. Their pulled-back opens are the identity and empty immersion. The finite computation is precisely `lem-cbc-proetale-extension-zero`; completion of identity/zero and its specified finite comparison give the restriction identities. The coefficient-passage definitions preserve these identities. Only after establishing them do I apply `lem-per-adic-heart-pullback-fibres`, whose statement explicitly gives the fibre comparison for any geometric point of a separated finite-type scheme and exact rational/common-stage pullback. A geometric point outside the open factors through the chosen closed subscheme because its defining ideal maps to zero in the point's field. Thus I do not apply a finite-type base-change package to an arbitrary non-finite-type geometric-point scheme, or use ordinary pro-etale stalk conservativity.

For step 5 I checked that `lem-trf-frobenius-open-square` includes geometric Galois Frobenius and all its powers, without claiming these maps are k-linear. `prop-functor-package` supplies the canonical base change and coefficient/Weil coherence. The output structure is explicitly j_!(theta) after that exchange; naturality proves that morphisms commute with it. The restriction comparison is the finite identity carried through the specified tower and field passages. The formula in `def-weil-local-frobenius-trace` uses the d-fold iterate, the geometric-point return and the point transport; each is preserved under the open factorization. I wrote this out rather than just asserting that Frobenius “transports”. No Frobenius-stable integral lattice for the input Weil sheaf is assumed: its Weil isomorphism is used after the functor has reached the field/common-stage category. The pair and morphism conventions are exactly `def-weil-weil-sheaf-complex`.

For step 6 the needed assertion is precisely the statement of `lem-dl-a1-constructible-fibres-exact`: constructible adic coefficient fibres are exact and jointly conservative, and a short sequence is exact iff every fibre sequence is. This includes the Weil version. Natural stalk comparisons identify the maps, not just the objects. For step 7 I checked the numerical definition of purity in `def-weil-punctual-weights`; the upper inequality is stated inline. An open immersion preserves residue fields at points of the open, so the same eigenvalue is measured against the same q_x. The zero complementary fibre has no eigenvalues; no spurious weight is assigned to an eigenvalue zero.

I tested the empty open, identity open, zero sheaf, a disconnected open, and an open with nonempty boundary. The zero sheaf is pure of every weight by the universal eigenvalue definition. No density, lissity, smoothness or properness of j was used. The closed-point/generic-point distinction is kept throughout. All steps are shorter than 2000 characters; the coefficient comparisons and Frobenius compatibility that would otherwise hide lemmas are explicit existing-node citations.

## Unfinished work

None in the one-level split. Existing unsplit dependencies remain their own future items. No new node was split recursively.
