# Worker report: nt-target-poincare-isiso

## Files written

- dag/nodes/sec-poincare-duality/nt-target-poincare-isiso.json: existing statement preserved byte for byte; four-step assembly, 2114 characters in proof text.
- dag/nodes/sec-poincare-duality/lem-pd-compactification-projection-inverse.json: new statement, unsplit, no Mathlib match. Canonical compactification projection, its actual proper/open normalizations, full-subcategory restriction, explicit inverse and naturality.
- dag/nodes/sec-poincare-duality/lem-pd-condensed-hom-chain-realization.json: new statement, unsplit, no Mathlib match. Conditional Hom-chain bijection on the precise condensed categories, its explicit counit/evaluation formula, and identification with postcomposition by the specified pairing transpose.
- citations.json: one exact statement quotation for every node used by every assembly step.
- report.md: this repair report. searches.jsonl is the unmodified output log of msearch.py. returned-proof.json retains the returned seven-step proof for the repair audit.

## Attachments

None. I searched WeilConjectures for the exact blueprint tag and for isIso_poincareMap and the Poincare map notion. There is no project declaration stating the entire target with this coefficient object, geometric hypotheses, boundedConstructible predicate and chosen purity map. The generic CategoryTheory.Verdier.isIso_exchange_of_isIso (PoincareDuality/Abstract.lean:227) proves exchange invertibility, not this geometric target or the explicit Hom-chain representative as a named declaration. The e calculation is local inside its proof, not an attachable declaration. CategoryTheory.Verdier.isIso_toIhomUnit (Abstract.lean:268) proves the unit identification, only one factor of the target.

The current ProjectionFormula.lean has isIso_boundedConstructibleExceptionalProjectionMorphism (line 774), its naturality declarations and the definition of the compactification map. These cover the isIso and naturality clauses of the first new node but not its independently normalized ringed-topos map identification and explicit inverse formula as a named theorem. I read the proper and open definitions and the compactification composition, rather than treating an unspecified isomorphism between endpoints as the specified map. The new node intentionally extracts the returned canonical-normalization argument. It is not recorded as a finished proof merely because the current Lean proves a subset of its clauses.

## WANTED

WANTED: literature/upstream-master-20261017/WeilConjectures/PoincareDuality/Poincare.lean, boundedConstructibleSmoothPurityIso, poincareMap and isIso_poincareMap, for nt-target-poincare-isiso. This source named in the retained node is absent from this machine. Its exact target statement and seven-step proof are retained in the live DAG. The current read-only project supplies Abstract.lean and ProjectionFormula.lean; I read their maps and compared the factor order. The proof remains marked agent-origin. No source was downloaded or invented and no repository file was written.

## What was wrong and what changed

The return requires spreading the existing 5554-character proof over at least two new comparable statement-only tasks. It does not ask to change the target statement, the coefficient category, or the proof route. The original sandbox contained only dispatcher marker files, not the claimed prior delivery. I therefore recovered the retained reviewed split from the current read-only DAG, including all source records, searches, blueprint fields and maintainer metadata. The delivery tool rebases only split-owned fields on the current server head; no local git command was run.

The compactification normalization in old Step 2 and the Hom-chain calculation in old Steps 3-4 have become two distinct, comparably sized tasks. The first has a 2790-character self-contained statement, the second 2279 characters. Each has status unsplit, proof [], proof_deps [], proof_origin null and actual logged searches. They can be worked on independently: the second takes an arbitrary natural family of projection isomorphisms for fixed K as a hypothesis, without depending on the first new node or on a result about purity. Neither concludes Poincare duality or introduces smoothness. The target assembles these inputs and still proves invertibility of the specified exchange using the explicit two-sided Yoneda inverse, before dealing with purity and the tensor unit.

The required new statement-only tasks are extractions expressly requested by the human re-split return. In particular the canonical-map comparison in the first task and the two-adjunction representative calculation in the second are not replaced by phrases such as “the same calculation” or “transport”. The tasks specify the exact maps and identities that the future proofs must establish. Their original arguments are copied without abbreviation below, as the worker's proof material, not as proof steps inside their statements.

## Coverage of every former argument

- Former Step 1: the assembly's Step 1 still fixes the same condensed categories and all three restricted adjunctions. The two new statements also introduce these objects and their hypotheses independently.
- Former Step 2: lem-pd-compactification-projection-inverse carries the actual proper mate, the open unit/lax/counit comparison, their independently specified ringed normalization, the composition comparison, full-subcategory inclusion, invertibility and naturality. Its displayed inverse makes the precise direction of every factor explicit. The complete old argument, including det-thm-sfb-proper-base-change-rational (3), the module/ringed comparison and the open projection input, is retained below for that task.
- Former Step 3: lem-pd-condensed-hom-chain-realization carries all five Hom bijections, their direction, domains, the projection precomposition and naturality. Its hypothesis of invertibility is supplied by the first new node only when assembling the target.
- Former Step 4: the same Hom-chain node specifies b_B(h) both as the counit/evaluation composite and as Phi composed with h. The naturality rewrite and currying argument remain verbatim below. Thus the canonical exchange is identified, not merely some isomorphism of the objects.
- Former Step 5: assembly Step 2 explicitly produces r using B=D and proves its second inverse identity using B=E. Neither test object is outside the restricted category.
- Former Step 6: assembly Step 3 retains the inverse of the chosen purity isomorphism, its fully faithful preimage, functorial inverse identities and the verification that ell is invertible on X from ell different from char(k). No normalization is changed and no independent coefficient realization is assumed.
- Former Step 7: assembly Step 4 retains the Hom test of the transpose of the left unitor, its inverse unitor, the explicit representability inverse argument and the exact three-factor definition of PD_p.

## Sources read and reuse searches

For the projection task I read the entire Open immersions, sheaves and Derived version paragraphs of literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-projection.proof.md, and (3) of sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-rational.proof.md. I read the actual current module-object definitions in lean/WeilConjectures/PoincareDuality/ProjectionFormula.lean: properProjectionMorphism, openImmersionProjectionComparison, leftDerivedUpperStarCompactificationIso, exceptionalProjectionMorphismOfCompactification, its right naturality, and the bounded-constructible restriction. The source assertions used to identify the proper/open canonical maps are explicitly in lem-pd-module-ringed-topos-derived-comparison; the open isomorphism is already in lem-pd-condensed-open-exceptional-projection-formula and the proper factor in lem-pd-condensed-proper-projection-formula. These are proof inputs for the future unsplit task, not new copies of those inputs. The compactification statement is about their composed normalized map and its inverse, not a new proof of either factor.

For the Hom-chain task I read the displayed chain and its naturality/representability paragraph in literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-tensor-hom/sk-thm-sf-tensor-hom.proof.md, and the actual adjunction, exchangePairing, exchange and isIso_exchange_of_isIso definitions/proof in lean/WeilConjectures/PoincareDuality/Abstract.lean. The blueprint's common-stage coefficient hypotheses are not asserted to imply anything about the different condensed category: the Hom argument is reconstructed using the condensed adjunction nodes read below. The retained source/ancestry follows the original target; blueprint_refs.py ancestor prints None for this seeded target, so the new nodes' from.node is null and via is [nt-target-poincare-isiso], just as the existing extracted open/comparison nodes do.

Before creating either node I searched the whole DAG for exceptionalProjectionMorphismOfCompactification, boundedConstructibleExceptionalProjection, Hom/curry/exchange and inverse/comparison terms, read the relevant statements, and ran blueprint_refs.py search for projection formula, exchange, compactification projection, Hom chain, counit formula, exceptional projection and adjunction bijections. I read the item's chapter and its recorded sk-thm-sf-verdier-exchange unit. The original six-functor route is preserved and no unit realization fields change: this seeded target is not the unit's key node.

The two leanfinder phrasings, leansearch, successful Loogle pattern and source grep for each task were actually run by msearch.py and the recorded result digests are from searches.jsonl. Failed first Loogle patterns (unknown identifier) are retained in the log but not claimed as successful absence evidence. The corrected searches returned generic adjunction equivalences and single currying lemmas. I inspected Mathlib/CategoryTheory/Monoidal/Closed/Basic.lean:153, 332 and 354, and Mathlib/Condensed/Light/InternallyProjective.lean:53-87. homEquiv_apply_eq only identifies one tensor-Hom transpose; ofEquiv_curry_def requires a monoidal equivalence; ihomPoints is a free-object/point-section calculation. None states the exceptional projection or the two-geometric-adjunction Hom-chain representative. The second phrasings returned Profinite.Nobeling projection formulas and ParametrizedAdjunction generic Hom bijections, not these statements. Existing target searches were retained, not invented or repeated.

## Not duplicates

lem-pd-compactification-projection-inverse vs lem-pd-condensed-proper-projection-formula: the existing statement inverts only the proper projection factor at j_!K; the new task identifies and inverts the full chosen-compactification composite, its canonical section-module normalization, inclusion and B-naturality.
lem-pd-compactification-projection-inverse vs lem-pd-condensed-open-exceptional-projection-formula: the existing statement concerns the open adjunction unit and open comparison Q; the new task concerns the composite with proper pushforward and pullback composition, including its normalized inverse and restricted target map.
lem-pd-compactification-projection-inverse vs lem-pd-module-ringed-topos-derived-comparison: the existing statement identifies ordinary/derived operations, actual tensor maps, and the individual projection mates; it does not assert the full compactification projection invertible or give its composite inverse.
lem-pd-compactification-projection-inverse vs det-lem-int-tensor-projection: the existing immersion projection isomorphism does not give the proper/open compactification composite with its actual module-object map and inverse.
lem-pd-compactification-projection-inverse vs nt-target-poincare-isiso: the new lemma contains no purity, orientation, internal Hom, exchange or Poincare morphism, and works for arbitrary f and K,B, without smoothness.
lem-pd-condensed-hom-chain-realization vs lem-pod-hom-chain-counit-formula: the existing statement assumes the fixed four-stage finite-field finite-Tor datum with completed/rational/common-stage conventions; the new one assumes the exact condensed internal-module boundedConstructible categories over arbitrary positive-characteristic k, and an arbitrary natural P for fixed K. There is no coefficient realization equivalence in either statement that makes one a specialization of the other.
lem-pd-condensed-hom-chain-realization vs lem-sf-tensor-hom: the existing statement is an endpoint exchange isomorphism with the common-stage finite-Tor hypotheses; the new one is a conditional exact Hom-bijection/counit formula in the different condensed categories, with no finite-field restriction.
lem-pd-condensed-hom-chain-realization vs lem-pod-global-duality-map-identification: that node concerns absolute/global duality and point-fibre comparisons, not the conditional relative Hom representative on condensed internal modules.
lem-pd-condensed-hom-chain-realization vs nt-target-poincare-isiso: the new lemma assumes a natural projection family and has no purity, Tate twist, unit specialization or Poincare morphism. It supplies the map-identification calculation; the target still constructs the exchange inverse and assembles the orientation and unit factors.

## Review by Q59

I checked the returned head as retained in the live node against the current project statements. There was no retained report or searches.jsonl in the sandbox at startup. I preserved the item's entire existing statement, metadata and search records, and only edited its split-owned proof/report fields. There is no statement dispute or silent strengthening of the target. The missing archived Poincare source is explicitly WANTED above; the available current Abstract.lean verifies the map definitions and the actual factor order.

For assembly Step 1 I opened sk-def-sfb-dc-restricted-functors and verified that it actually restricts U,G, tensor and internal Hom, gives U left adjoint to G and the tensor-Hom adjunction, and restricts composition; the needed preservation holds for exactly the condensed Qlb coefficient. sk-def-sfb-dc-upper-shriek states F left adjoint to V on those same categories, constructed using the chosen compactification. def-sfb-dc-tensor-hom-adjunction fixes the left tensor factor and the restricted Hom bijection. The first new statement asserts invertibility/naturality of exactly the canonical P^c and identifies its component for the chosen compactification with PF^!. These statements supply all the data Step 1 uses. I did not infer a projection theorem just from an adjunction definition.

For assembly Step 2 I read the second new statement with all objects introduced: its hypotheses are satisfied by Step 1, including all test objects in C_S. Its formula is b_B(h)=Phi h with the same counit/evaluation pairing as the target, not the reverse exchange. Its first and third arrows are inverse adjunction bijections, and its fourth precomposes with P_B, which has the correct domain FK tensor B. I checked the explicit inverse argument by composing the equations: Phi r=1_D implies Phi(r Phi)=Phi, and injectivity for B=E gives r Phi=1_E. This is elementary and requires no uncited Yoneda theorem or small-index colimit assertion.

For assembly Step 3 I opened nt-target-poincare-tate-bc: it supplies tateTwistDerived(X,ell,d)[n] with the identical boundedConstructible predicate, assuming only ell invertible on X. The field-characteristic check verifies that assumption, even if X is empty. I opened nt-target-smooth-purity-qbar: it gives the chosen smooth-purity isomorphism in the ambient category for smooth pure dimension d and exactly these condensed coefficients, and the target already specifies its bounded-constructible preimage. Thus the proof uses exactly that preimage and its inverse, not a newly chosen purity map. A functor preserves both inverse equations directly.

For assembly Step 4 I checked def-sfb-dc-tensor-hom-adjunction again with K equal to the tensor unit. By naturality of currying, Hom(B,u) corresponds to composing with the left unitor on the unit tensor B. Composing with its inverse is the inverse Hom function. The explicit argument in Step 2 then proves u invertible. The target defines PD as G(purity inverse), then G(u), then Phi, in just the order checked in Abstract.lean. The composite inverse is the reverse-order composite of their inverses, so no extra categorical theorem is hidden here.

For each new statement I checked small cases: f=id with identity compactification, j=id and an empty open, K=0 or B=0, d=0 for the assembly, and K=L=unit for the Hom statement. The first inverse reverses a: Lj^*Lq^* to Lf^*, Q^{-1}, and alpha in the correct order. When the categories are zero, the equalities reduce to the unique morphisms. For the Hom statement with identity adjunctions the chain reduces to currying/uncurrying; with a nonidentity natural P its value still uses P_B, and naturality moves h through P_E exactly as the formula requires. No properness of the full f, algebraic closedness of k, common-stage coefficient equivalence, perfectness or smoothness is being tacitly assumed.

I checked B-E of delivery-errors: new nodes are self-contained statement-only tasks with actual source places, single TeX escaping, correct concept definitions in stmt_deps, actual logged searches, filled blueprint provenance and no cycles introduced by citing the parent. I distinguished every plausible duplicate above, including the different coefficient categories of the existing Hom-chain nodes. Each assembly citation is supported by its exact statement in citations.json. Each non-elementary fact in the assembly is one of those cited statements; representability, inverse preservation and the unitor argument are written out. No non-elementary assembly step exceeds 2000 characters. All former proof arguments remain below verbatim for the two new workers, and the new-task partition follows the human's requested workload distribution rather than replacing the argument with one large restatement. No SGA source or SGA trace route has been used.

## Unfinished work

Only the explicitly requested unsplit proofs of the two new nodes remain for other workers. They are delivered statement-only. No Lean was written, compiled or built, and no agent was started. Delivery validation and push are recorded at the end after the tools finish.

## Retained argument material, verbatim from the returned split

This material belongs in the report, not in the statement-only nodes' proof fields. It is retained so no argument is shortened, blurred or lost during re-splitting.

### Former step 1

Work entirely in the target's condensed categories C_T = D_cons(T,Qlb). Write F=Rp_!, U=Lp^*, G=Rp_* and V=Rp^!, and write H_T for the restricted internal Hom. By [sk-def-sfb-dc-restricted-functors] and [def-sfb-dc-tensor-hom-adjunction], U is left adjoint to G and A tensor - is left adjoint to H_T(A,-) in these full subcategories. By [sk-def-sfb-dc-upper-shriek], F is left adjoint to V on the same categories. Thus every object and Hom set in the following argument lies in C_X or C_S; no comparison with the common-stage Qlb category is being assumed.

Uses: sk-def-sfb-dc-restricted-functors, def-sfb-dc-tensor-hom-adjunction, sk-def-sfb-dc-upper-shriek.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-tensor-hom/sk-thm-sf-tensor-hom.proof.md; displayed Hom-adjunction chain, reconstructed in the condensed categories without coefficient-category identification.

### Former step 2

Use the target's chosen compactification $p=q\circ j:X\xrightarrow j Z\xrightarrow q S$. By [sk-def-sfb-dc-lower-shriek], $F=Rq_*j_!$; by [sk-def-sfb-dc-restricted-functors], $j_!K,Lq^*B$ are bounded constructible and $U\cong Lj^*Lq^*$ by the specified composition comparison. The definition of $PF^!$ is the proper projection arrow followed by $Rq_*$ of the inverse open projection and this composition comparison:
$$Rq_*j_!K\otimes B\longrightarrow Rq_*(j_!K\otimes Lq^*B)\xrightarrow{Rq_*(q_{j,K,Lq^*B}^{-1})}Rq_*j_!(K\otimes Lj^*Lq^*B).$$
Here the module-object proper arrow is adjoint to $(\varepsilon\otimes1)\delta_q$, whereas the open map $q_j$ is adjoint to $\mu_j(\eta_K\otimes1)$. By [lem-pd-module-ringed-topos-derived-comparison], the actual module-object $\delta_q$, its inverse lax map $\mu_j$, the derived adjunctions and the tensor/pullback identifications agree with the ringed-topos structures. Thus the proper arrow is exactly the map $\alpha$ to which clause (3) of [det-thm-sfb-proper-base-change-rational] applies. It is invertible. By [lem-pd-condensed-open-exceptional-projection-formula], the displayed canonical $q_j$, including its use of the actual lax structure, is invertible. Applying $Rq_*$ to its inverse preserves its inverse identities. Composing these two isomorphisms with $Lj^*Lq^*\cong Lp^*$ proves invertibility and naturality of this specified $PF^!_{K,B}$. All objects and inverse morphisms are in the full bounded-constructible subcategories by the cited restriction statements.

Uses: sk-def-sfb-dc-lower-shriek, sk-def-sfb-dc-restricted-functors, det-thm-sfb-proper-base-change-rational, lem-pd-condensed-open-exceptional-projection-formula, lem-pd-module-ringed-topos-derived-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-tensor/det-lem-int-tensor-projection.proof.md; Open immersions and Derived version, combined with the specified proper and open comparison maps; canonical-map equality delegated to lem-pd-module-ringed-topos-derived-comparison.

### Former step 3

Fix K=Qlb_X and L=Qlb_S, and put E=G H_X(K,VL) and D=H_S(FK,L). For every B in C_S there is a bijection b_B:Hom_S(B,E) → Hom_S(B,D), formed by the following chain in this direction:
Hom_S(B,G H_X(K,VL)) = Hom_X(UB,H_X(K,VL)) = Hom_X(K tensor UB,VL) = Hom_S(F(K tensor UB),L) = Hom_S(FK tensor B,L) = Hom_S(B,H_S(FK,L)).
The first and third equalities are the two geometric adjunction bijections; the second and fifth are the tensor-Hom adjunction bijections of [def-sfb-dc-tensor-hom-adjunction]. The fourth precomposes with the isomorphism PF_{K,B} from Step 2. The cited restricted adjunctions justify each change of Hom set. They apply to all B in C_S, including E and D, since their functors and internal Hom have codomains C_T. The chain is natural in B because its constituent adjunction bijections and PF are natural.

Uses: sk-def-sfb-dc-restricted-functors, def-sfb-dc-tensor-hom-adjunction, sk-def-sfb-dc-upper-shriek.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-tensor-hom/sk-thm-sf-tensor-hom.proof.md; displayed Hom-adjunction chain, reconstructed in the condensed categories without coefficient-category identification.

### Former step 4

The bijection b_B is postcomposition with the specified exchange Phi:E → D, not merely with some isomorphism of these objects. Write epsilon:UG → id and epsilon!:FV → id for the two counits. For h:B → E the chain sends h to the tensor-Hom transpose of
FK tensor B --PF_{K,B}-→ F(K tensor UB) --F(1_K tensor (epsilon_{H_X(K,VL)} composed with U(h)))-→ F(K tensor H_X(K,VL)) --F(ev)-→ FVL --epsilon!_L-→ L.
Naturality of PF in B rewrites the first two arrows as (1_{FK} tensor h), followed by PF_{K,E}, followed by F(1_K tensor epsilon_{H_X(K,VL)}). The remaining evaluation and epsilon! arrows are unchanged. This is exactly the pairing used in the target to define Phi, precomposed with 1_{FK} tensor h; naturality of currying therefore gives b_B(h)=Phi composed with h. No duality comparison of coefficient categories is used.

Uses: .

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-tensor-hom/sk-thm-sf-tensor-hom.proof.md; displayed Hom-adjunction chain, reconstructed in the condensed categories without coefficient-category identification.

### Former step 5

Since postcomposition with Phi is bijective on every Hom_S(B,-) by Steps 3-4, Phi is invertible. Explicitly, surjectivity for B=D gives r:D → E with Phi composed with r=id_D. Then Phi composed with (r composed with Phi)=Phi=Phi composed with id_E, and injectivity for B=E gives r composed with Phi=id_E. Thus r is a two-sided inverse. This is the elementary representability argument, with the inverse and both identities written out.

Uses: .

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-tensor-hom/sk-thm-sf-tensor-hom.proof.md; displayed Hom-adjunction chain, reconstructed in the condensed categories without coefficient-category identification.

### Former step 6

Let T=Qlb_X(d)[2d]. The target's pur_p:VQlb_S ~= T is the bounded-constructible preimage of the smooth purity isomorphism supplied by [nt-target-smooth-purity-qbar]. Its inverse T → VQlb_S is therefore invertible. Applying G preserves its inverse identities, giving an isomorphism GT → G VQlb_S. The target already supplies T as an object of C_X through [nt-target-poincare-tate-bc]. Its current hypothesis that l is invertible on X holds here: the image of l in the field k is nonzero since char(k) differs from l, so its inverse in k pulls back to an inverse in every structure sheaf of a k-scheme. Its conclusion uses precisely the upstream boundedConstructible predicate of the target; no new choice of purity or of normalization is made.

Uses: nt-target-smooth-purity-qbar, nt-target-poincare-tate-bc.

Source: literature/upstream-master-20261017/WeilConjectures/PoincareDuality/Poincare.lean; boundedConstructibleSmoothPurityIso and poincareMap.

### Former step 7

For A=VQlb_S, the unit-Hom map u:A → H_X(Qlb_X,A), the transpose of the left unitor Qlb_X tensor A → A, is an isomorphism. Indeed, for any B, adjunction identifies postcomposition Hom(B,A) → Hom(B,H_X(Qlb_X,A)) with h mapping to h composed with the unitor on Qlb_X tensor B, which is a bijection with inverse precomposition by the inverse unitor. The same explicit inverse argument of Step 5 makes u invertible; applying G preserves this. By the target's definition, PD_p is G(pur_p inverse), then G(u), then Phi at K=Qlb_X,L=Qlb_S. All three factors are isomorphisms by Steps 5-6 and the present argument, so their composite PD_p is an isomorphism.

Uses: def-sfb-dc-tensor-hom-adjunction.

Source: literature/upstream-master-20261017/WeilConjectures/PoincareDuality/Poincare.lean; poincareMap and isIso_poincareMap, factors through purity, unit transpose and exchange.

## Validation

The first required server dry run exited 0: OK (not pushed) deliver/Q59/nt-target-poincare-isiso at 675f015d2a8, preflight passed. The gate ran on the delivery overlay on the Weil server; no local checker or compiler was run. A final dry run follows the correction of the report's source line references.
