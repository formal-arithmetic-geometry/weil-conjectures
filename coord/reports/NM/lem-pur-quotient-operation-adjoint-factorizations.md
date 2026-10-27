## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-quotient-operation-adjoint-factorizations.json`: statement; eight proof steps; not in Mathlib. Statement and all inherited metadata retained. No new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for all eighteen step/node citations (sandbox validation artifact).

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and for quotient/adjoint, semilinear, tensor and K-flat terminology. The ordinary restrict-scalars adjunction declarations do not state the item's prescribed chain comparisons or its normalized derived identities. No exact project attachment was found.

## WANTED

None. The sources needed for this split are present.

## Findings and corrections

The item was statement-only, with no earlier sandbox split or report. Its statement is correct as written; I have not changed its objects, coefficients, hypotheses or conclusions. Its `blueprint.from` accurately records the inherited former coefficient-twists step 5, quotient-expression steps 8–9; the ancestor command confirms `def-weil-frobenius-coefficient-twists`. Whole-blueprint searches for scalar, adjunct and semilinear returned more specialized coefficient-system statements but no interchangeable version of this actual-transition claim. The current blueprint's coefficient-twists text was read; its present short Frobenius statement no longer contains the historical extracted argument, so I retained the explicit extraction provenance instead of inventing a current paragraph number.

The two points requiring care are that inverse-image unit generators are not all literal target-site sections, and that an arbitrary isomorphism of derived objects is insufficient for the specified mate. Step 5 proves equality through the inverse-image adjunction on all source-site objects; steps 4 and 7 use the existing normalization lemma and explicit ring-isomorphism transport. The tensor identity is proved for the actual semilinear maps on the original output complexes, without assuming normalized systems. All steps are shorter than 2000 characters.

The required Mathlib searches were run with `msearch.py` and logged in `searches.jsonl`. Two semantic phrasings, Loogle, LeanSearch and two source grep patterns were read. The hits `SheafOfModules.PullbackConstruction.adjunction` (PullbackContinuous.lean:79), `PresheafOfModules.pullbackComp` (Presheaf/Pullback.lean:131), and `ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars` (ChangeOfRings.lean, source at the scalar-adjunction namespace) give ordinary adjunctions or composition, not this theorem. Light-condensed monoidal hits concern a different category and lack the chain/derived actual-transition assertion. Existing item search records were retained, and only the queries actually run in this session were appended.

## Unfinished work

None in the one-level stage-1 split. This delivery writes no Lean and runs no compiler or build. It leaves the existing cited nodes responsible for their own proofs.

## Not duplicates

No new nodes. I reused `lem-pur-kflat-total-tensor-model` for tensor closure, `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` for pullback and coefficient-change closure, and the existing scalar-mate normalization and ring-transport nodes. In particular I did not create separate nodes for the two generator calculations, inverse-pair checks, or clauses of the item itself.

## Review by NM

I read Stacks `sites-cohomology.tex` at Tag 07A2 (lemma-tensor-product-K-flat), Tag 0G7E (lemma-pullback-K-flat), Tag 07A4 (lemma-pullback-tensor-product), and Tag 07A6 (lemma-adjoint), and `sites-modules.tex` Tag 03EL (lemma-tensor-product-pullback). These justify the representative route; the explicit actual-transition factorization is an agent argument using their normalized interfaces, so `proof_origin.by` is `agent`. No SGA source is used.

For step 1 I opened both cited node statements. The total-tensor node explicitly includes flat terms, unbounded direct-sum totalization and K-flatness. The ringed-topos tensor/pullback node explicitly preserves flat-term K-flat complexes and allows arbitrary structural ring maps. It applies to both geometric pullbacks and to identity geometric morphisms with ring maps q and q'. Thus a nonflat quotient is allowed; flatness of each extension as a module over the original ring is never assumed.

For steps 2 and 3 I read the tensor definition and signed-total definition. Their sheafification and coproduct descriptions give precisely the maps used. I checked balancing for both B_m factors, balancing over B_n, the two inverse composites, and both terms of the differential. Scalars have degree zero, so moving a or b introduces no Koszul sign; the unchanged input degree p gives exactly the sign (-1)^p. The semilinear tensor transition respects r on either input, and its adjunct agrees with the composite on every bidegree. These are elementary calculations, not new general lemmas.

For step 4 I read the full statement of `lem-sfb-kflat-scalar-comparison-normalization`: its ordinary coequalizer comparison points in the opposite direction from chi and preserves insertion of one; its inverse is the specified derived mate. I take that inverse. I also read `lem-pur-ring-iso-derived-transport`, which provides action transport, flat/K-flat preservation, localized-map compatibility and the tensor/unit comparisons. The two c_j are ring isomorphisms by the item's hypotheses, and their compatibility with q and q' is exactly what identifies the transported scalar action. Naturality with the differential gives the chain comparison. No inverse-image equivalence or scheme-isomorphism assumption is being inserted.

For step 5 the only citations are the sheaf-tensor definition and the geometric-morphism definition. The latter gives the inverse-image Hom adjunction. I wrote out the two values on (1 tensor u) tensor a, then justified detection of equality through that Hom bijection, at every source-site object. This avoids assuming surjectivity of source-section images on a target object. The same calculation checks semilinearity through the coefficient square.

For step 6 I read clause (2) of `lem-pur-sheaf-ring-derived-coefficient-adjunction`, which explicitly identifies the adjunct of a localized semilinear chain map with x tensor a mapped to a times t(x), without flatness or boundedness. I applied it separately to U, V and K. I read `lem-weil-pbc-site-derived-tensor-descent`, whose statement gives the natural comparison on both chain-map variables. The ringed tensor/pullback node computes the canonical derived comparison by the ordinary K-flat tensor model, and `lem-sfb-ringed-derived-monoidal-comparisons` explicitly says that comparison is strong monoidal. Thus localization gives the specified mu and actual derived maps, rather than an unrelated abstract isomorphism.

For step 7 the same adjunct normalization applies with coefficient map q' and flat-term K-flat F_m, already established in step 1. The pullback node computes the image of the chain map on K-flat representatives. The scalar-comparison normalization identifies Q(chi) with the inverse coequalizer comparison's mate, and ring transport preserves both the localized maps and tensor units. Their statements supply exactly the maps used, including the isomorphisms c_m,c_n. I have not used the proof of a cited node in place of its statement.

Step 8 writes the actual inverse composites; it uses only the already proved identities and functoriality of localization. I tested zero modules, zero rings, identity coefficient maps, identity geometric morphisms, a nonflat quotient Z to Z/2, and homogeneous odd-degree inputs. In the odd-degree test the sign remains (-1)^p on both sides, and no scalar acquires a sign. For the nonflat quotient the source extension of a flat-term K-flat model remains K-flat over the new ring by the cited pullback theorem, which is the property actually required. For arbitrary non-isomorphic input adjuncts, all factorization equations still hold; invertibility is asserted only in the final conditional clause. The statement is self-contained in its coefficient square and does not rely on an unspecified whole-system input.

I checked delivery-errors B–E: no hollow definitions or new statements are introduced; no restatement nodes are created; every non-elementary ingredient is a cited existing node, and `proof_deps` is exactly the union of step uses. Each cited node was opened, and `citations.json` copies verbatim the statement parts actually needed. Generic tools from other units are declared in `split_report.tool_uses`; they do not replace the unit's purity route. No chapter or unit file is changed. The item carries no statement dispute, and no statement or hypothesis has been weakened.

The first delivery dry run rejected two citation excerpts as shorter than its 40-character minimum. I replaced them with the full signed-total definition and also expanded the derived normalization excerpts to include the full clauses used. The mathematical proof was unchanged.
