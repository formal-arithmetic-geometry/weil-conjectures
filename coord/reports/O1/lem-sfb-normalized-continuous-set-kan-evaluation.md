## Worker report

Item: lem-sfb-normalized-continuous-set-kan-evaluation. Group O1, 2026-10-22. Stage 1 only; no Lean was written or compiled, and the shared repository was only read.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normalized-continuous-set-kan-evaluation.json: statement node, six proof steps, status split; its statement and stmt_deps are unchanged. Mathlib has the generic adjunction tools, not this normalized relative-scheme comparison.
- citations.json: 16 step/dependency entries, quoting verbatim the statements actually opened.
- report.md: this report and signed self-review.

## New nodes

None. All the mathematical tools already have DAG nodes. In particular the canonical sheafification-unit assertion is already lem-weil-pbc-proetale-sheafification-wcontractible-sections; it would be a duplicate to create it again. There are zero new Mathlib leaves.

### Attachments

None. Whole-project searches in lean/WeilConjectures for the item tag, normalized continuous-set realization, continuous/profinite/Kan notions found no declaration giving the complete item. The related Sheaf.Paper.TotallyDisconnectedCoefficientRealization theorem existsUnique_continuousSetRealization has sorry, and only packages the parent realization theorem. Its docstring supplies the intended normalization, but is not evidence of a finished attachment.

### WANTED

None: the HRS and Bhatt--Scholze PDFs and the Stacks source used here are available locally.

### Defects corrected and limits

The imported item had no proof. The split now distinguishes the presheaf cocone map alpha, the sheafification unit eta, the unit-normalized isomorphism e to the specified p_X^*, and sigma. The equation alpha = sigma e eta makes the normalization and the direction of the comparison explicit.

The inherited blueprint.from.node was null even though its place and via chain explicitly named det-thm-sf-ctf-stability-direct-images. tools/blueprint_refs.py ancestor reported this null. The created.item chain reaches lem-sfb-admissible-direct-image, whose existing from.node is det-thm-sf-ctf-stability-direct-images; its created.item is a Lean module name rather than a DAG id. I repaired only this item's ancestor to that existing blueprint id and retained the via chain/place. No chapter, unit, or other node was changed. This is a provenance repair, not a change of proof route.

The proof is marked agent-written: HRS Example 3.1 explains the intended realization, and BS Lemmas 4.2.12--4.2.13 supply the component route, but neither literally states every normalization assertion in this item. The extra adjunction and representative arguments are written out rather than attributed verbatim to HRS.

## Not duplicates

No new nodes and hence no new/existing pairs. Searches of the whole DAG and blueprint for Kan, sheafification, connected components, continuous functions, normalized continuous, and the Stacks tags found the tools reused in the proof. No existing blueprint node states this complete normalized comparison. This item refines the existing parent realization theorem, not a new copy of it.

## Review by O1

I read HRS Example 3.1, printed p.6, and BS Lemmas 4.2.12 and 4.2.13(1), printed pp.30--31. The former identifies pulled-back coefficients with continuous functions and explicitly mentions factoring through components on contractible affines; the latter gives the continuous-function sheaf and component quotient calculation, and the presheaf inverse-image argument. The assertion here is set-valued and retains the given Hausdorff/totally-disconnected hypothesis. I also read Stacks sites.tex lemma-adjoints-u (00VE), lemma-adjoint-sheaves (00WX), proposition-sheafification-adjoint (00WH), and categories.tex lemma-transformation-between-functors-and-adjoints (0B65), whose Hom-set argument explains the specified mate/normalization. Mathlib Sites/Pullback.lean:59--87 and Functor/Flat.lean:302--322 confirm the generic adjunction and pointwise-colimit interfaces; they do not state the relative scheme-site item. Searches were run with msearch.py in two natural-language phrasings and with Loogle, LeanSearch and grep; the actual logs are preserved in searches.jsonl and appended to mathlib_searches without inventing queries. All services used in this session answered successfully.

For step 1 I opened the complete statement of lem-weil-pbc-profinite-point-pullback: it fixes a^*, p_X^*, the locally constant integer test scheme, and the geometric morphism. def-weil-proetale-inverse-image explicitly states that scheme direct image is evaluation on base change. def-weil-pbc-composite-adjunction supplies exactly the composite right adjoint and Hom bijection. lem-sfb-relative-profinite-test-labels states the natural identification X[S] = X times a(S). Together these give R_XG(S)=G(X[S]) including arrows. This verifies continuity by the actual right-adjoint restriction, without assuming an extra topology theorem about a_X.

For step 2 the statement of lem-sfb-pointwise-kan-colimit explicitly uses I_U^op, not I_U: the diagram arrows are restrictions H(S') to H(S). Its smallness hypotheses are met by the compatible small skeletons already in the item's statement. lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction explicitly provides the set-sheaf adjunction and says its Hom bijection is Kan followed by sheafification; step 1 checks its hypothesis. lem-weil-pbc-conjugate-iso-unit-equation states the unique isomorphism carrying units for two left adjoints of the same right adjoint, which is exactly what we need. None is merely a fully faithful Yoneda result or a definition being used as a theorem.

For step 3 I checked that the relative-label node's statement has r_{X,T}|X[v]| = v r_{X,S}. This is the precise equality proving naturality of b to b r. def-sfb-continuous-set-presheaf explicitly makes restrictions precomposition. The existing pointwise-Kan statement supplies the colimit universal property, and the sheafification definition states unique factorization into any sheaf. The elementary part is the written two-composition calculation and the universal-property application; it introduces no separate continuity or sheaf theorem. Both function presheaves are assumed sheaves here, so no descent theorem for arbitrary D is smuggled into this step. The equality bar-alpha = sigma e follows from the unit normalization in step 2, and fixes the representative map without a free choice of section isomorphism.

For step 4 I read lem-sfb-continuous-set-descent-components. Its statement explicitly gives a profinite component quotient and the precomposition bijection for every totally disconnected target on qcqs U. Affineness ensures qcqs; a profinite S is an allowed target. The relative-label node states both existence of phi_U and the implication r phi = g q implies phi = X[g] phi_U, exactly what the argument takes from it. The pointwise-Kan node fixes the opposite orientation: g goes from (T,phi_U) to (S,phi) in I_U, hence it gives the relation from b to b g in the colimit diagram. No finite-image assumption on b or D is used.

For step 5 the descent/components node's precomposition bijection supplies surjectivity. Injectivity is checked on the actual representatives produced by step 4, using surjectivity of the quotient q_U, not an unproved assertion that an arbitrary Kan diagram is filtered. I tested U empty (T empty, the normal coefficient function is unique for every D), D empty with U nonempty (there are no normal representatives), a connected nonempty affine (T a point), and noncompact D (each continuous function still factors through the quotient; no compactness of D was invoked). Finite/disconnected U likewise retains all component values.

For step 6 I opened lem-weil-pbc-proetale-sheafification-wcontractible-sections and its Lean source packaging PointLanSheafificationProperty. Its statement covers sets, not just modules, and says the canonical sheafification map on this exact relative-test Kan presheaf is an isomorphism. It defines weak contractibility by exactly the epi-on-sections condition used in this item. Thus it is a direct application with F = underline D, followed by cancellation of the bijections in alpha = sigma e eta. I did not infer the canonical unit's bijectivity merely from existence of an abstract section isomorphism. The two off-unit generic inputs (the specified point inverse image and the canonical sheafification-unit theorem) are explained in split_report.tool_uses for maintainer review; they keep the unit's continuous-coefficient route.

All six proof steps are below 2000 characters. No step moves the item or one of its clauses into a new lemma. I checked the reachable dependency paths of the existing component, affine-evaluation and sheafification inputs for a return to this item: none was found. I preserved all pre-existing fields and mathlib searches, changed no source statement, and introduced no new definitions or unsplit nodes. The resumed delivery dry run completed successfully: OK (not pushed), preflight passed, at 9af8d014b00. I reread all eleven distinct cited node statements and checked all 16 citation quotes against the current read clone; none was missing or nonverbatim. The item statement and statement dependencies still agree exactly with the live unsplit node. The final delivery reruns the server preflight before pushing.
