# lem-sp-ringed-site-tor-flat-model

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-ringed-site-tor-flat-model.json: item, statement; split into six proof steps, unchanged statement, no Mathlib match.
- citations.json: a verbatim statement quotation for every node cited by every proof step.
- searches.jsonl: actual msearch.py results; fresh searches were added to the item's pre-existing search records.

New nodes: 0. New Mathlib leaves: 0. No Lean written or compiler run.

## Attachments

None. I searched the specified slopmaster2 WeilConjectures tree for the exact blueprint tag and flat-model terminology. The generic DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat in CategoryTheory/DerivedCategory/FlatModel.lean:300 is a related abstract result, but assumes a monoidal Grothendieck abelian category with functorial flat resolution and identifies flatness and derived tensor through that structure. Its text does not itself instantiate the equivalence for arbitrary variable ring sheaves on arbitrary sites. The pro-etale theorem in SixFunctors/ProEtale/Derived/FlatModel.lean:56 has a particular site and a bounded-constructibility hypothesis. Neither was represented as an exact attachment under this brief's requirement.

## WANTED

None.

## Corrections and observations

No statement dispute or source error was found. At first the shared repository had no assigned node; its delivery-tool fetch refreshed the shared snapshot and supplied the item. The initial dry run had already exited with “no node files”; no concurrent delivery was launched. The proof was then prepared from the actual newly available node, retaining its source, inherited searches, creation metadata and blueprint ancestry. The absence diagnosis is resolved.

The source's reverse implication first chooses a bounded-above flat model and repeatedly removes its top degrees using the flat-kernel theorem. Here the existing bound-preserving replacement theorem is applied to a representative already zero above b; it gives that same intermediate object in one step and avoids introducing either a new flat-kernel node or a hidden induction. This is a change below the blueprint node, within the same flat-resolution/truncation argument.

I made the single-variable tensor calculation explicit. The item cites a derived-tensor theorem formulated for two K-flat flat-term representatives; that theorem alone does not directly say that an arbitrary M[0] may be left unresolved. Step 1 uses a resolution C -> M[0], the tensor-cone isomorphism, K-flat acyclicity and the quasi-isomorphism/cone criterion to justify precisely this passage. It is a short deduction from existing statements, so it is a proof step rather than a new lemma node.

The source for lem-pc-bounded-above-flat-kflat-site calls its result 06YS in its metadata; reading the Stacks label and tags map identifies the bounded-above-flat theorem as Tag 06YQ, lemma-bounded-flat-K-flat. Our proof-step source cites that correct tag. The existing node's statement, which is what is used, is correct. I did not modify that other node.

## Searches and reuse

Read the actual results of all fresh msearch.py searches: LeanFinder in two phrasings, Loogle, LeanSearch and grep. LeanFinder returned bounded derived representatives and Grothendieck-category facts; LeanSearch returned ordinary-module flatness criteria. The grep found DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:180; I read lines 165–195. It supplies a bounded representative, with no termwise flatness clause, so it is not a match for the item. No unavailable service was recorded as no match. Existing search records were retained.

Searched the entire DAG for 08G1, the last-one-flat and tor-amplitude labels, bounded flat replacement, K-flatness and cokernel flatness. Ran blueprint_refs.py search 'flat model' and ancestor for the item. The blueprint's flat-model nodes have finite-coefficient/constructibility or particular-site hypotheses and do not state this arbitrary-ringed-site result. Reused the existing site flat-opcycles criterion and bounded-above flat replacement instead of creating duplicates.

## Not duplicates

No new nodes. In particular no new copy of the already existing bounded-flat replacement, site K-flatness or flat-opcycles criterion was made.

## Review by Q86

I read Stacks sites-cohomology.tex, lemma-tor-amplitude (08G1), lines 12432–12481 and the preceding lemma-last-one-flat (08G0), together with Section 06YL around the K-flat and bounded-flat lemmas and the definition of derived tensor (06YU). I checked the label/tag mapping for 06YP and 06YQ. The ringed-site statement matches the source: arbitrary sheaf of commutative rings, every module sheaf as test object, integers a <= b, with no assumption of constructibility, enough points or constant coefficients. I also read the chapter record, sk-prop-sp-integral-adjunction unit record and the current det-sp-integral-direct-image-tower statement/proof. The generic flat-model input serves that ancestor's projection-formula paragraph and does not replace an adjunction or tower step.

For step 1 I opened the statements of lem-pc-kflat-resolution, lem-pur-quasi-iso-cone-acyclic, lem-pc-tensor-mapping-cone-iso, def-pc-kflat-complex, lem-pc-sheaf-modules-tensor-closed and lem-weil-pbc-site-derived-tensor-descent. The resolution supplies flat terms and K-flatness, both inputs of the descent computation. The cone lemma is for arbitrary sheaf-module complexes, not only ring modules; its cone is on the second tensor factor, exactly as used. The two cone tests and the definition of K-flatness prove the comparison in three direct deductions. No exactness of sections, stalk criterion or assumption that M is flat enters this argument.

For step 2 the statement of lem-pc-bounded-above-flat-kflat-site applies because P is termwise flat and zero above b. I checked def-pc-tensor-complex-sheaves: its direct-sum degree formula has exactly one summand when the second complex is M[0]. The degree support and vanishing follow immediately. It is an elementary application of those stated facts, not an uncited K-flat theorem.

For step 3 the ordinary tensor-unit isomorphism comes from the actual statement of lem-pc-sheaf-modules-tensor-closed. Flatness of R is the identity-functor instance of def-pc-flat-sheaf-modules, and step 1 computes tensor with R for a flat-term K-flat resolution of K. I opened def-sbc-standard-tstructure-derived-category and checked that its statement explicitly includes the equivalence between upper cohomological vanishing and existence of a representative zero above b; I do not take a representative theorem from the proof of a definition that lacks it in its statement.

For step 4 I read all of lem-pc-kflat-bounded-flat-replacement's statement. It gives a replacement zero above the supplied integer N, not merely some unspecified upper bound. Our L satisfies its hypothesis with N=b. Its quasi-isomorphism is inverted by the explicitly cited localization definition. Neither its functoriality clause nor its proof is used.

For step 5 I read the exact statement of lem-weil-pbc-site-flat-opcycles-tor-criterion: it assumes a small site, flat terms and universal ordinary-tensor exactness in degree n-1; it concludes flatness of the cokernel in degree n. Our site is small in the module universe, all F terms are flat, and step 1 plus (1) gives the required vanishing with n=a. The tensor symmetry exchanges a degree-zero factor with no Koszul sign. Thus every hypothesis, including testing every module sheaf, holds. This avoids replacing a sheaf-Tor assertion by an ordinary-ring Tor assertion.

For step 6 I checked the abelian cohomology and complex definitions. The good lower truncation has a cokernel term B, not the generally nonflat kernel or cohomology sheaf. I wrote its induced differential and checked its square using d^2=0. The cohomology formula at a and equality of images at a+1 verify the quasi-isomorphism; higher degrees are unchanged and lower cohomology is already zero. Flatness and the two degree bounds then give exactly (2). This is the elementary truncation calculation in the source, not a new independent lemma.

I checked zero K (the zero model), the zero coefficient ring, empty sites/topoi, the one-point site, negative endpoints, and a=b. In the latter case F^(a+1)=0, so the bottom cokernel is H^a(F) and the model has the single flat term in degree a; no strict inequality a<b was used. For zero F no “largest nonzero degree” is needed. I checked that proof_deps is the union of the uses, all quotes are actual statement text and no cited dependency reaches this item. No non-elementary step exceeds 2000 characters (the six lengths are 918, 420, 660, 497, 758 and 1173), so there is no long step concealing a further claim. The six generic off-unit statements are declared in split_report.tool_uses with their purposes. There are no new statement-only nodes to audit. These are my substantive B–E checks; all needed non-elementary ingredients are cited statements, not source tags alone.

## Unfinished

Nothing mathematical. Required server dry run and push follow this report.
