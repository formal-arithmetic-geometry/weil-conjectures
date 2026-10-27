# Worker report: lem-route-sp-rational-twist-map-id

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-route-sp-rational-twist-map-id.json`: statement; split into four identity-normalization calculations, using existing nodes only. No Mathlib match for this particular rational Tate transition.
- `citations.json`: six verbatim statement excerpts for every proof-step citation.
- `report.md`: this report. `searches.jsonl` is the actual msearch.py log.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the item tag, `spRationalTwistMap_id`, `spRationalTwistMap`, and `spIntegralTwistMap`: no completed declaration matches. The exact existing declaration is `AlgebraicGeometry.ProEtale.spRationalTwistMap_id`, `lean/Sheaf/Paper/ProEtaleTateTwists.lean:359`; its proof is `sorry`. It is retained as the existing Lean binding and is not an ATTACH.

## WANTED

None. This is an explicit elementary assembly proof written by NH from the published unique-map interfaces and the latest blueprint construction. No SGA source is used.

## Repairs and findings

The imported node was only a provisional machine-made Lean signature and docstring with empty dependencies. I supplied its complete mathematical statement, all parameters, the actual underlying abelian-sheaf morphisms, and the integral and rational normalizations. This is not a change of mathematical claim. In particular the Lean signature assumes only a scheme X and primality of ell. I did not add the blueprint's ell-invertibility assumption: identity coherence of these constructions holds for every X, although local freeness needs invertibility. The powers are indexed positively (n in natural numbers means exponent n+1).

The aggregate definition `sk-def-sp-tate-twist` currently depends on this item through `lem-sp-ell-point-reduction-ring-map`. Using it as an ordinary statement dependency would create a cycle. Instead the statement writes the concrete constructions and cites the independent definitions and unique-map nodes. All these independent nodes were opened and inspected; a read-only dependency traversal confirmed they do not reach this item. The aggregate definition is source context only. I have not edited it or its unit. The latest blueprint includes the alternative Qbar tensor description; no Qbar comparison or local-freeness assertion is needed for this identity.

The four normalization nodes are filed in the smooth-purity `sk-prop-an` unit by automatic route attribution. They describe precisely these same maps in `Sheaf.Paper.ProEtaleTateTwists`. I declared them in `split_report.tool_uses`: their characterizations are used as interfaces for the identity law, with no replacement of the unit's construction route. The coefficient-map nodes are definitions/tools. No new auxiliary lemma restates this item or one of its clauses.

## Sources and searches

I read the chapter and unit records, the latest blueprint chapter and `sk-def-sp-tate-twist/_section.md`, and `lean/Sheaf/Paper/ProEtaleTateTwists.lean` through the integral/rational constructors and all four uniqueness statements. The identity theorem docstring explicitly prescribes uniqueness first for integral limits and then for the rational tensor quotient. I also read the upstream coefficient inclusion implementation and its identity lemma in `WeilConjectures/CategoryTheory/RingObjects/Condensed/FiniteSubextension.lean:80-104`, and the pullback coefficient-map definition and identity in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean:93-106`.

Blueprint searches ran for `identity transition`, `Tate twist`, `spRationalTwistMap`, `field-extension transitions`, and `rational Tate`; DAG concept and Lean-name searches found the existing four normalization nodes. The blueprint ancestor command returns `sk-def-sp-tate-twist`. None of the search results is another statement of this identity law, so `same_as` is empty.

All seven new Mathlib searches were actually run with msearch.py and are preserved verbatim in the item and searches.jsonl. Two different semantic phrasings were tried. LeanSearch found ordinary module identity scalar extension; LeanFinder found cyclotomic-character identity, cotangent functoriality, localization maps and p-adic limit formulas; Loogle found no TateTwist and did find general Functor.map_id. I read the candidate `ModuleCat.extendScalarsId` at `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:954-974` and the Functor identity axiom at `Mathlib/CategoryTheory/Functor/Basic.lean:47`. The former is an isomorphism for ordinary modules extended along an identity ring map. Here the coefficient ring map O_E -> E is fixed and generally is not the identity, and the theorem concerns a separately chosen abelian-sheaf transition characterized by its normalization. Neither candidate is a one-line specialization giving the item's statement. Functor identity is used only as an elementary axiom in the written calculations. The source grep found no TateTwist/spRationalTwistMap in Mathlib. No service was unavailable.

## Not duplicates

No new nodes were created. All needed non-elementary characterizations were already in the DAG.

## Review by NH

I reviewed sections B through E of delivery-errors against the actual files. The source for the item is the latest blueprint's integral inverse-limit and rationalization paragraph, read together with the exact identity docstring and constructors in ProEtaleTateTwists. The claim is equality of underlying abelian-sheaf morphisms, exactly as the Lean signature states; no new semilinearity, local freeness or base-change hypothesis has been inserted. There are no new nodes to source or test.

For step 1, `def-sfb-qlbar-subextension-map` explicitly states that its identity inclusion is the identity, and `def-sfb-coefficient-map` explicitly makes the pulled-back coefficient map the functor image. The functor identity axiom therefore gives i=id. `lem-route-sp-integers-map-exists-unique` says both that the candidate must be a ring-object morphism and that its square over E_X -> F_X commutes. I checked the identity preserves unit and multiplication, and both sides of this square are c_E. Thus uniqueness applies with E=F without further hypotheses.

For step 2, `lem-route-sp-ell-map-exists-unique` states exactly the square between the two integral reductions, not merely that a quotient map exists. With a=id the identity quotient morphism satisfies this square since both sides are r_E,n. Its uniqueness gives b_n=id for each n, including n=0 (exponent one). This step invokes no unstated epimorphism cancellation: that work belongs to the cited uniqueness theorem.

For step 3, `lem-route-sp-integral-twist-map-exists-unique` gives a unique underlying abelian-sheaf map with all the displayed positive-level projection composites. After step 2 the tensor factor is id tensor id, so the required composite is p_E,n itself. The identity on L_E satisfies that equation for every n. I checked the finite root factor is unchanged, and that there is no appeal to local generators, a different constant-ring model, or an unproved identification of limits.

For step 4, `lem-route-sp-rational-twist-map-exists-unique` gives uniqueness among abelian-sheaf maps with the exact extend-pi equation. Its source is the unbalanced tensor E_X tensor_Z L_E and its target is the balanced scalar-extension quotient. With i=id and g=id its right hand side is q_E, which is also id composed with q_E. The identity therefore has the prescribed normalization and uniqueness proves the conclusion. This uses the normalization theorem itself, not a hidden proof of epimorphicity or a global assertion that all sheafified tensor sections are pure tensors.

Every proof citation has a verbatim excerpt in citations.json; each excerpt was checked by literal containment in the cited statement. All four proof steps are elementary applications of already cited uniqueness with the candidate identity and explicit equations, each shorter than 2000 characters. I checked the small cases E=Q_ell, arbitrary ramification, ell=2, the empty scheme, and schemes where ell is not invertible: the calculations remain valid, including when the root sheaves vanish or are not locally constant. The tensor identity and uniqueness do not require nonzero sections. No statement dispute arose. The dependency union equals proof_deps and no new nodes, missing citations, inline non-elementary subclaims, or source-route changes remain.

## Unfinished work

None in the stage-1 mathematical split. Lean remains untouched and uncompiled, as required. Server dry-run and delivery results are recorded below when available.

## Validation

The first dry run requested a longer excerpt for the identity coefficient inclusion (the short identity formula was verbatim but under its 40-character minimum). I replaced it with the complete functoriality sentence, including both identity and composition formulas. No mathematical change was needed.
