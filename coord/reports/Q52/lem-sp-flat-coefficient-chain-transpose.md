# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-flat-coefficient-chain-transpose.json`: statement, split; six proof steps; Mathlib searches find infrastructure but no exact match or one-line specialization. The original statement and all inherited source, creation, chapter, unit and blueprint ancestry fields are retained.
- `citations.json`: fourteen entries, one for each step/node citation, with verbatim statement excerpts.
- `searches.jsonl`: actual search-command output log, retained alongside the inherited search records in the item.
- `report.md`: this report and the direct-delivery review.

## New nodes

None. Zero new nodes and zero new Mathlib leaves. All non-elementary ingredients already have DAG nodes. The ordinary chain-adjoint calculation, the combination of two naturality squares, and the naturality calculation for pairs of maps are elementary proof steps, not nodes.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag, flat coefficient/chain transpose terminology, derived transposition, scalar/pullback and coefficient-change maps. There is no project declaration stating the entire item. `SixFunctors/ProEtale/ModuleObject/ChangeOfCoefficients.lean` has related comparisons, but its derived coefficient-change section explicitly assumes exact/flat coefficient extension and concerns pro-etale condensed coefficients. It does not state the present arbitrary-ring small-etale representative calculation. The generic derived-adjunction normalization theorem is likewise not the item.

## WANTED

None. The Stacks source and blueprint source needed here are present locally.

## Findings and changes

The item was unsplit with an empty proof. Its inherited Mathlib searches and ancestry were preserved. There was no earlier sandbox node or report to reuse. The statement is well typed and is unchanged; in particular, `lambda` is the inverse of the normalized scalar/pullback map, so the map to evaluate is `c = lambda^{-1}`, not `lambda`.

The item's source points to Stacks 0GL6, `more-etale.tex`, `remark-Rf-lower-shriek-change-of-rings`. I read that remark: it gives the motivating coefficient compatibility of compact support, not a proof of this stronger formal chain calculation for arbitrary scheme maps and arbitrary rings. The delivered proof is explicitly agent-written, using the K-flat and canonical-adjunction results in `sites-cohomology.tex`. It does not apply the torsion, quasi-compactness, separatedness or properness hypotheses of the motivating remark to this item.

The chapter record is `sec-smooth-purity`; the inherited unit is `sk-thm-sf-compatibility`, whose coefficient clause says coefficient comparisons preserve tensor reassociation and adjunction units/counits. This calculation is a tool used beneath the chart coefficient comparison of `det-sp-reduction-exceptional`, through `lem-sp-et-proet-coefficient-compatibility` and `lem-sp-acyclic-flat-proper-coefficient-model`. It changes no chapter or unit route. I read the current blueprint file `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.md`, which states the chart comparison and counit condition; the proof here supplies a lower-level normalization calculation rather than replacing that route.

## Search audit and reuse

Ran the required `msearch.py Q52 lem-sp-flat-coefficient-chain-transpose` commands using leanfinder, leansearch, loogle and grep. The seven exact queries and their actual results are appended from `searches.jsonl` to `mathlib_searches`. Both semantic phrasings were read. The first finder search returned etale algebra/differential results; the second returned ordinary sheaf pushforward isomorphisms and exact-functor localization. LeanSearch returned abstract derived adjunction infrastructure. Loogle returned the ordinary sheaf module adjunction or no hits. The first grep found none of the named comparisons; the broader grep found abstract derived adjunction and left-derived infrastructure.

I read Mathlib `CategoryTheory/Functor/Derived/Adjunction.lean`, especially `derivedε_fac_app` and the hypotheses of `Adjunction.derived`, and `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`, the ordinary pullback and pullback/pushforward adjunction. These are not a one-line proof of this item's fixed sheaf scalar/pullback representative formula: the relevant comparison normalization and its computation on K-flat representatives still have to be supplied. Existing DAG nodes provide those statements and the proof performs that computation. The inherited searches from the item's creation were not represented as searches by Q52.

Searched the whole DAG for K-flat pullback, scalar/pullback representative, chain transpose and Tag 0G7E, and opened the relevant candidate statements. Ran `tools/blueprint_refs.py ancestor` and searches for `scalar pullback`, `chain transpose`, `scalar/pullback`, `scalar extension`, `K-flat`, `transpose`, and `coefficient chain`. The narrow scalar/pullback and transpose-combination searches found no exact blueprint node. The broad hits concern coefficient packages, other operations, or restricted finite/integral coefficient domains; none duplicates the present all-rings flat-chain normalization calculation. The existing nodes actually stating the needed general tools are cited instead of creating copies.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs to justify. The proof reuses `lem-weil-pbc-ringed-pullback-preserves-kflat`, `lem-pur-derived-change-of-rings`, `lem-pur-left-derived-from-kflat-class`, `prop-weil-pbc-inverse-image-modules-exact`, `def-pur-etale-scalar-pullback-iso` and `lem-sp-etale-derived-chain-transpose`.

## Review by Q52

I reviewed the node and the statements of all six cited nodes with the Stacks sources open. The source places read were `sites-cohomology.tex`, Tag 0G7E (`lemma-pullback-K-flat`), Tag 06YY (`lemma-derived-base-change`), Tag 06YT (`lemma-derived-tor-quasi-isomorphism-other-side`), Tag 07A4 (`lemma-pullback-tensor-product`), and Tag 0FPI (`lemma-adjoints-push-pull-compatibility`), as well as `more-etale.tex`, Tag 0GL6 and the blueprint file named above. The statements of the K-flat, exact geometric pullback, scalar comparison and chain-transpose nodes specify the additional category and normalization data used here. No SGA source is used.

Step 1 uses the precise conclusion of `lem-weil-pbc-ringed-pullback-preserves-kflat`: pullback of a K-flat complex with flat terms is again such a complex without flatness of the coefficient map. Apply it to the geometric map and to identity-topos coefficient changes separately. The original hypotheses supply K-flatness AND flat terms for both P and K; exactness of geometric pullback is not substituted for that theorem. `lem-pur-derived-change-of-rings` gives the invertible scalar representative maps on P, K and r_A^*P. `lem-pur-left-derived-from-kflat-class` explicitly provides a natural transformation for the total left-derived functor, which is the naturality of those representative maps; I am not extracting a naturality assertion from a proof sketch. `prop-weil-pbc-inverse-image-modules-exact` states exactness of the ordinary geometric functor and its module adjunction for ANY scheme morphism and commutative ring. I cite `lem-sp-etale-derived-chain-transpose` separately for the canonical termwise derived-pullback identification: this is explicit in its statement, rather than attributed to an ordinary exactness result alone.

Step 2 uses the actual displayed normalization in `def-pur-etale-scalar-pullback-iso`, not merely the existence of an isomorphism between the functors. I checked the arrow directions: c is lambda inverse, rho runs from r_B^*P_B to F_W(r_A^*P), and the formula has sigma_(r_A^*P) after c. The geometric representative identifications are the exact termwise ones already fixed. Thus substituting those identifications in the cited normalization gives exactly the equation written. No extra comparison theorem is hidden here.

Step 3 uses naturality of the natural left-derived comparison from `lem-pur-left-derived-from-kflat-class` at h, and substitutes Step 2. I checked the common intermediate object F_W(r_A^*P) and the three representative maps. The resulting arrow is Q((h tensor 1) rho), with the order in the statement. The chain-map property of rho is just naturality at the differentials; that of h tensor 1 is functoriality. These are the elementary calculations written in this step, not additional geometric lemmas.

Step 4 uses the ordinary adjunction explicitly stated by `prop-weil-pbc-inverse-image-modules-exact`. Naturality of its Hom equivalence takes the two sides of the chain equation to exactly the two sides of the chain equation for pi. I checked that the counit here is the ordinary counit on K_B; the final equality follows from the inverse Hom bijection, degree by degree. No exactness of direct image and no acyclicity is being inferred.

Step 5 cites `lem-sp-etale-derived-chain-transpose`, whose statement really supplies e(alpha Qf) = Q(f-flat), and says it is valid for arbitrary complexes with no boundedness, acyclicity, flatness or properness. With M=P_B and f=pi, Step 4 identifies f-flat with a_h. Step 3 then gives the asserted m_h after the fixed representative identifications. Inverting the bijection e is elementary, and the non-elementary compatibility is exactly the cited node, not an uncited derived-adjunction claim. There is no need to assume that K_B is K-injective or r_*-acyclic.

Step 6 checks the naturality clause explicitly rather than saying it transports. First the natural rho isomorphism and the equation vh=h'r_A^*u give v_B a_h=a_h' r_B^*u_B. Ordinary adjunction naturality gives the pi equation, and the stated naturality of alpha and e in `lem-sp-etale-derived-chain-transpose` gives the displayed derived equation. The representative natural transformation and natural c then give the equation on the original objects. Every use of naturality is either part of a cited statement or the defining naturality property of the displayed natural transformation/adjunction; no coefficient-change theorem is assumed.

I checked B--E against these files. There are no new unsplit statements to test for missing objects, proof text in statements, duplicate definitions, same-tag duplication or false generality. The item's original statement introduces its objects and retains all its definition dependencies. No clause was moved into a new node; the calculation remains in the six item steps. Every cited fact is in the cited statement, and the fourteen citation entries were checked as verbatim substrings. `proof_deps` is the union of the step uses. Off-unit general tools are explained in `split_report.tool_uses`, without adding the maintainer's top-level `tool_uses` field. All proof steps are under 1000 characters, so none exceeds the 2000-character long-step threshold or hides a source's omitted lemma.

For edge cases I checked r=id and phi=id: rho and the normalized c give the usual scalar map or the ordinary derived chain-transpose formula. With P=0, K=0, or h=0 the Hom-bijection formulas give zero on both sides. For a genuinely nonflat example A=Z, B=Z/2 and P,K concentrated in degree zero with free terms, the equations use tensor and its representative, not exactness of tensor. For unbounded P,K the proof uses only the stated K-flat comparison and the arbitrary-complex transpose theorem; no bounded truncation or convergence argument enters. Empty schemes and the zero coefficient ring cause no additional condition. These checks required no statement correction. The main correction to the imported material was supplying the missing proof and distinguishing the motivating compact-support remark from the formal facts actually used.

## Unfinished work

No mathematical part of this item remains. The cited unsplit nodes remain their own queue items; they were not split recursively. The server-only preliminary review_split passed. The first delivery dry run rejected a natural-isomorphism quote of fewer than 40 characters; I replaced it with the complete defining natural-isomorphism passage. On rereading C4 I also added the explicit chain-transpose citation in Step 1 for the termwise derived identification. Every citation quote now has at least 40 characters and is verbatim. Full validation and direct delivery follow.
