# Q118: lem-trf-roos-cone-compositor-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-roos-cone-compositor-descent.json — existing statement, split into eight proof steps; Mathlib verdict: no match for the entire assertion.
- citations.json — fourteen verbatim cited-statement excerpts, indexed by proof step.
- report.md — this report.

No new nodes and no Mathlib leaves are created. The statement, statement dependencies, source and blueprint ancestry are unchanged. The proof adds only existing dependencies. All eight steps are shorter than 2000 characters.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and the words Roos, roos, compositor and their combinations found no declaration asserting this entire comparison theorem. Existing Roos comparison and homotopy declarations do not provide its F/G/U compositor assertion. No sorry declaration is treated as a finished proof.

## WANTED

None. The required local Stacks sources and the current blueprint are present.

## Findings and corrections

The item was statement-only, with no repair note and no previous sandbox split. Its statement is mathematically consistent. There is a coordinate convention to explain: def-weil-strict-roos-model uses (old y,old z) with differential (-dy-u z,dz), whereas the item and lem-cbc-exact-product-functor-strict-limit use (x,y) with differential (dx,u x-dy). Step 1 explicitly changes coordinates to (old z,-old y); the ordinary-limit inclusion becomes (iota,0). This is an identification of the specified construction, not a statement change.

The product comparison is an isomorphism using preservation of countable products and the tower isomorphism b_i. The shift and signed differential identities are computed explicitly. Composition is proved separately on both cone summands; the argument does not infer equality of derived maps from their evaluations. The final equality follows by naturality of the normalized Roos isomorphism and cancellation, followed by fully faithful precomposition with localization.

Mathlib searches were run through msearch.py only and read before recording. Six logged searches cover two distinct semantic phrasings, Loogle piComparison, product grep, mapping-cone grep, and LeanSearch. Results included piComparison and its projection equation, preservation-of-product declarations, mappingCone.mapHomologicalComplexIso and exact-derived-factorization declarations. These are ingredients rather than exact matches or one-line specializations of the entire F/G/U assertion. The original Q129 searches in the existing item were retained verbatim as inherited records; new Q118 records are copied from searches.jsonl. Read source locations include Mathlib/CategoryTheory/Limits/Shapes/Products.lean:650-664, Limits/Preserves/Shapes/Products.lean:52-88, and Localization/Predicate.lean:278-363. No new node requires an absence or duplicate claim.

## Review by Q118

I read Stacks sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok, including the proof choosing a K-injective tower, its ordinary termwise limit, the two products and the kernel inclusion. I also read categories.tex, Tag 04VG, lemma-properties-left-localization: this source gives functor factorization but does not itself state fully faithful precomposition on natural transformations. For that stronger assertion I read the existing localization node's full statement and its Mathlib source, Predicate.lean:278-363, including liftNatTrans_app, comp_liftNatTrans, liftNatIso and natTrans_ext. I read the current main-20261015 blueprint thm-trf-l-function-euler-product.proof.md, Step 1, Global powers, where the required composition compatibility occurs, and the chapter and unit records. The split stays on that route and proves its generic comparison input.

For step 1 I opened lem-weil-pbc-exact-functor-derived-factorization and lem-weil-tower-category-levelwise-abelian: their statements respectively give exact termwise functors and preservation of quasi-isomorphisms, and levelwise kernels/cokernels in towers. Hence F_i^Tow is exact under the actual hypotheses. I opened def-weil-strict-roos-model and checked its differential and inclusion explicitly under (x,y)=(old z,-old y). No unproved claim that an arbitrary additive functor preserves products is used: countable-product preservation is a separate hypothesis; only finite biproducts use additivity.

For steps 2 and 3 I opened def-weil-inverse-system: its morphism equation is exactly w_n b_{n+1}=b_n F(v_n). Step 2 uses only the defining product property, the assumed preservation and naturality of b_i; an explicit inverse to psi is given. Step 3 computes the nth projection of both shift composites and both outputs of the signed differential. Its reference to the strict-model definition supplies precisely the diagonal cone construction, not a theorem about derived evaluations.

Step 4 is elementary product uniqueness after two written projection calculations. Naturality of d moves the product projection past d; the assumed b/d/t compatibility at M^q makes the resulting components equal. No extra fact is taken from an uncited node. Step 5 opens the same strict-model statement for its diagonal action on strict maps. Naturality of d for the two biproduct inclusions makes d_H diagonal; the two diagonal entries are step 4 in degrees q and q-1. Both off-diagonal entries are zero. These are strict complex identities, including the negative shifted differential checked in step 3.

For step 6 I opened lem-weil-strict-roos-comparison and lem-cbc-exact-product-functor-strict-limit and read their full statements. The former explicitly supplies a natural isomorphism on the unbounded derived category and its K-injective inclusion normalization. The latter explicitly states the conjugation formula and its equality with the ordinary-limit/resolution comparison. It applies with both sites equal to the given small site and F=F_i: exact countable products, exactness and product preservation are all hypotheses of this item. Naturality with b_i and the strict diagonal formula identify their composite with kappa_i, so the claimed canonical comparison is fully specified. Both results are generic tools from other units, declared in split_report.tool_uses with their precise use.

For step 7 the exact-derived-factorization node explicitly states that termwise functors invert quasi-isomorphisms. The normalized Roos node explicitly says its construction descends and its comparison is natural. Clause (2) of the localization node states unique lifting of natural transformations, including isomorphisms and composition. These statements apply to the actual functors after precomposition with Q_S, and establish naturality for all derived morphisms, not just strict chain maps. For step 8 I expanded the two conjugated comparisons: the intermediate theta_Y factors cancel inside F_1; naturality of theta along U(t_M) leaves the strict whole-cone compositor; naturality of d along theta_X then gives the left side. The localization node's clause (3) detects equality of natural transformations on localized complex objects. This is not faithfulness of any tower evaluation.

I checked sections B-E of delivery-errors against the actual files: no new statement-only node or hidden sublemma is introduced, no clause is repackaged as a dependency, and no cycle is introduced by the existing generic inputs. Every cited node's statement was opened, and citations.json contains verbatim passages from those statements. The eight steps range from 642 to 1192 characters; none hides an argument behind a long step. The four non-elementary steps cite the exact comparison or localization theorems they use; the elementary steps write their component calculations.

Small checks: for zero U or the zero complex all displayed maps have zero source and target and the identities hold; for identity functors and identity b,d,t the product and cone comparisons are identities and the derived formula is theta^{-1}theta=1. Constant towers with identity transitions retain the second signed summand, so the check does not silently discard it; zero transition towers give u=1, and the signed calculation still holds. For a nontrivial scalar natural automorphism d with b_0=b_1=1, compatibility forces b_2=d^{-1} (when t=1), and the product and cone compositor equations both give 1, confirming the orientation of d. Unbounded complexes cause no infinite sum or totalization in this proof: each degree has just two product summands. No boundedness, constructibility, or existence of K-injectives in S has been added. No SGA source is used.

## Unfinished work

None for this stage-1 split. Independent maintainer review remains part of the normal delivery process.
