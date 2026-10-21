# Q82: lem-pur-system-pushforward-restriction-transition

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-system-pushforward-restriction-transition.json`: item, statement, status split. The statement and its hypotheses are unchanged. Six proof steps; no new nodes and no new Mathlib leaves.
- `citations.json`: 18 step/node entries, each quoting a verbatim substring of the cited statement.
- `report.md`: this report. `searches.jsonl` is the search command's own log.

## Attachments

None. Searched the live read-clone `lean/WeilConjectures/` for the exact blueprint tag/id, semilinear systems, and pushforward/restriction transition notions; no declaration states this item. The module-object and adic declarations returned by the broader searches concern ordinary sheaves or other coefficient models, rather than this unbounded derived semilinear-system statement. No proof with sorry was treated as an attachment.

## WANTED

None. The source ingredients used are present locally.

## Corrections and scope

The imported item had a statement but no proof. I retained that statement, all imported metadata and earlier Mathlib search records, and supplied the argument. In particular I retained the scalar-transpose clause, the resolution normalization, arbitrary ring-sheaf towers, the case m=n, and the lack of flatness or normalization hypotheses. Stacks 0D6E itself states derived pushforward composition, not this system transition statement; the proof is marked agent-written and combines that comparison with existing system and mate theorems. No claim that a system evaluation detects all derived morphism equalities is used.

The nearest blueprint ancestor is `lem-weil-compact-support-representative-independence`, via `lem-weil-compact-support-reduction-tower-functor`. I read its current main-20261015 proof at `sec-six-functors-basics/sk-thm-sf-pf-field/lem-weil-compact-support-representative-independence.proof.md` and the current `sec-proetale-coefficients/sk-def-sf-operations/_section.md`, as well as the repository's chapter and unit records. This item supplies the direct-image transition identification implicit in the ancestor's first sentence, before forming the coherent compact-support reduction tower. It does not change a unit or chapter route. Whole-blueprint searches for semilinear, restriction-form, ring-sheaf-change, and coefficient projection found no blueprint statement equal to this one, so `same_as` remains empty.

Generic tools from other units are declared in `split_report.tool_uses`, with their purposes. The simultaneous-system theorem supplies the actual extension-form transition rather than merely an objectwise assertion. The general ringed comparison and mate laws supply the comparison normalization and formal conversion, which are not separate statements of this item's unit. No top-level `tool_uses` was edited.

## Mathlib searches

Ran LeanFinder twice with different phrasings, Loogle, grep, and LeanSearch through the required msearch.py command. All returned successfully; no service failure was recorded as absence. The exact query strings and the returned declaration names are appended to the preserved search records and appear in the command's searches.jsonl log. I read `ModuleCat.extendRestrictScalarsAdj` at ChangeOfRings.lean:885 and `SheafOfModules.pullbackPushforwardAdjunction` at Sheaf/PullbackContinuous.lean:60: both concern ordinary module categories. The second LeanFinder search also returned `CategoryTheory.LocalizerMorphism.rightDerivedFunctorComparison_fac`, which I read at Localization/DerivabilityStructure/PointwiseRightDerived.lean:71; it is a general factorization identity for a supplied localization comparison, and does not identify this system comparison or its scalar mate. None is an exact match or a one-line specialization for the item. The grep hit in Ring/CompTypeclasses.lean is only an introductory mention of semilinear typeclass inference.

## Not duplicates

No new nodes were created. I reused the existing coherent-section theorem, coefficient adjunction, canonical ring-change comparison, normalized composition theorem, geometric-interface definition and mate-pasting theorem. In particular I did not introduce separate nodes restating either transition clause of this item.

## Review by Q82

I read delivery-errors.md B through E in full and checked the proof against the actual node statements, rather than their dependency lists or their proofs. For sources I read Stacks sites-cohomology.tex, label lemma-adjoint (07A6), label lemma-derived-pullback-composition (0D6D), and label lemma-derived-pushforward-composition (0D6E), including their proofs. The two-factorization argument is the same composite-adjunction route as 0D6E. The extra scalar and system identifications are spelled out as agent arguments using existing statements. There is no SGA source in the argument and no new node whose source would need auditing.

Step 1 uses the statement of `lem-weil-pbc-ring-sheaf-change-adjunction` for d and its canonicity. I checked its compatibility equation with R=B_m, S=B_n, and the two source coefficient identifications equal to identities: it is precisely the pulled-back ring map, so the theorem needs no extra flatness. `lem-pur-sheaf-ring-derived-coefficient-adjunction` supplies both scalar adjunctions on the unbounded categories and exact restriction. `def-weil-size-convention` supplies small representatives in a common larger universe; no large indexing category is introduced.

Step 2 uses `lem-sfb-ringed-derived-monoidal-comparisons` specifically for its adjunction-compatible composition and identity comparisons, not just its monoidal assertion. Its statement explicitly says that the canonical composite adjunction is transported by the pullback and pushforward comparisons. The ring-change node identifies d with the same two-factorization comparison. `lem-coef-semilinear-derived-sections` supplies the specified b, and `def-coef-semilinear-geometry-derived` specifies that the coefficient-pullback comparison uses the localized underlying restriction identity. This checks that the coefficient square uses that specified comparison. I checked the orientations: alpha is S F_m to F_n T; d is p G_n to G_m q; chi=alpha inverse has conjugate delta=d inverse. Thus the proof does not silently interchange d and delta.

Step 3 cites the actual mate word in `def-weil-pbc-adjunction-mate` and the composite-adjunction formula in `lem-weil-pbc-mate-pasting`, together with the scalar adjunction theorem. I wrote out delta_L as p G_n(epsilon^S_L) composed with p(b_qL) composed with eta^T_{G_m qL}. The types run G_m qL to p T G_m qL to p G_n S qL to p G_n L. This is the composite-adjunction mate of chi. Neither inverse-preservation for arbitrary mates nor invertibility of b is asserted.

Step 4 is an elementary calculation from the displayed mate word and natural adjunction bijections. It writes out the transpose as G_n(epsilon^S_L) b_qL T G_m(a), applies naturality of b, and substitutes a sharp = epsilon^S_L S(a). Every intermediate map has the required source and target. The cited coefficient adjunction and mate definition state these bijections and the unit/counit conventions; there is no hidden comparison lemma here.

Step 5 uses exactly the extension-form transition sentence in `lem-coef-semilinear-derived-sections`. Its statement concerns the actual simultaneous derived direct image with specified evaluation isomorphisms. The restriction and extension transitions are adjoint by construction, so injectivity of the scalar Hom bijection from the coefficient adjunction transfers step 4 into the required restriction formula. This does not use a definition node as a substitute for the system-existence theorem and does not infer equality of system morphisms from evaluation.

Step 6 uses the explicit normalization sentence of `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`. In the factorization through the source coefficient change, the intermediate replacement is exactly qI to H, giving u_*qI to u_*H. In the other factorization, exactness of p identifies its derived functor with termwise p, and I already computes G_n. Thus d is the class of that forward arrow, and delta its inverse. The composition theorem supplies quasi-isomorphy. The identity clause of the adjunction-compatible comparison theorem and the system theorem give the m=n case. These statements have unbounded complexes and do not require restriction or evaluation to preserve K-injectives.

For small cases I checked m=n, the identity geometric morphism, a constant coefficient tower, and the zero complex. In the first three the corresponding comparison reduces to the identity and the formulas become the ordinary scalar-transpose identity; the zero maps remain zero. I also checked a nonflat tower with B_1=Z/2, B_2=Z/4 and identity maps above level 2 on the one-point site: the proof uses derived extension and exact restriction, and nowhere replaces derived tensor by ordinary tensor, so it imposes no false flatness condition. These are tests of the statement and proof conventions, not compiler runs.

B: no new statement-only node, no missing definition for a new object, no fabricated search, and the item keeps its blueprint ancestry. C: all non-elementary ingredients are cited statements with verbatim excerpts in citations.json; off-unit tools are declared. D: the proof carries the mate argument and uses existing theorems instead of moving either clause to a new node. E: the coefficient-square hypotheses, map orientations, unbounded scope, naturality, and identity case were checked above. Every proof step has fewer than 2000 characters, and none hides an additional geometric or homological assertion. No Lean file was written and no compiler, Lake, local DAG checker, or local preflight was run.

## Unfinished work

None in this one-level split. The existing prerequisite nodes retain their own stage status; this delivery does not claim that all their Lean proofs are finished. Final acceptance is subject to the required server dry run and maintainer review.
