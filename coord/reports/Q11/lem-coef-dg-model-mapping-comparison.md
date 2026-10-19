# Stage-1 repair: lem-coef-dg-model-mapping-comparison

## Files written

- dag/nodes/sec-six-functors/lem-coef-dg-model-mapping-comparison.json: item, split; statement, Lean record and proof route preserved.
- dag/nodes/sec-six-functors/lem-coef-dg-resolution-square-projection.json: new statement-only auxiliary lemma, unsplit; no Mathlib match.

## Attachments

None. Searched the whole read-only slopmaster2 WeilConjectures tree for the blueprint id and dg-model/mapping-comparison terminology, then for enriched, bifibrant, dgCategory, quasiEquivalence and resolution squares. No exact project declaration exists. The archived master tree also gives no declaration for the item. The existing audit says none on both branches. Ordinary quotient model homotopy categories do not constitute an attachment to this enhanced statement.

## Wanted literature

No additional external theorem is assumed here. The blueprint's coefficient adjunction motivates the argument but does not prove this general dg foundation. The proof remains agent-written, and the auxiliary node records that provenance explicitly. No SGA route is used. No available Stacks tag asserts the resolution-square/enhanced-localization lemma; no unrelated tag is supplied as its authority.

## What was wrong and what changed

The dedicated Q11 handoff in coord/returns/Q11.md names old steps 3, 5 and 8 (2773, 3106 and 2681 characters). The repository retains an earlier reviewed proof but resets its status to unsplit. There was no sandbox item or report to continue. I copied that proof, retained all its searches and citations, and extracted its genuine generic square-projection argument. Step 8's other hidden input already has a node: lem-coef-dg-quasifunctor-invariance. The new item has eleven steps of lengths 1991, 1063, 826, 1052, 1024, 1227, 956, 1785, 743, 1158 and 748. No non-elementary step exceeds 2000 characters. This is not just subdivision to evade the check: the pullback/cohomology and relative dg projection argument is now a separately stated lemma, and the coherent functor-category assertion is an explicit existing citation.

No statement dispute or target change was found. The item statement, existing source and blueprint ancestry, Lean audit and other maintained metadata are preserved. The unit statement is not this item, so no unit realization record was edited.

## Mathematical argument isolated in the new node

This argument is retained here for the future worker; the unsplit node itself carries only its statement. A pullback of a degreewise surjective quasi-isomorphism of complexes is again one. Indeed its kernel is the original kernel. To see that this kernel is acyclic, let a kernel cycle z in degree n bound da in the source, using injectivity on H^n. The image of a is a cycle; surjectivity on H^(n-1) supplies a source cycle c and target b with f(a)-f(c)=db. Lift b to t; then a-c-dt belongs to the kernel and bounds z. Conversely an acyclic kernel permits lifting target cycles (correct a lift by a kernel element bounding its differential) and proves injectivity on cohomology (subtract the differential of a lift of a proposed target primitive, then bound the resulting kernel cycle). Also a target closed degree-zero element lifts to a closed element by that correction.

Apply this to the Hom pullbacks in the new node. Componentwise differential and composition preserve t a=b s, and identities do also. Thus the projection has surjective quasi-isomorphisms on mapping complexes and is surjective on objects by the stated coverage hypothesis. It is a quasi-equivalence. Existing dg quasi-functor invariance gives the equivalences on derived functor categories. These identify the full subcategories inverting the marked arrows: one direction is immediate; conversely any marked arrow downstairs lifts to a closed square upstairs, which is marked by the definition of W_R. An upstairs functor inverting W_R corresponds to a downstairs functor, with an invertible coherent comparison; naturality on that lifted square shows the downstairs arrow becomes an equivalence. The enhanced localization universal property identifies the two localized categories, transformations and diagrams. Opposite dg categories give the dual orientation. This proof does not use the item's conclusion, its model structure or bifibrant objects.

## Searches and small cases

Read the complete search results logged in searches.jsonl. For the new lemma ran LeanFinder twice with different descriptions, Loogle for EnrichedCategory, LeanSearch for the dg resolution-arrow localization, and grep for dgCategory/QuasiEquivalence. The hits concern ordinary model-category resolutions, ordinary localizations and plain enriched categories. Read Mathlib/CategoryTheory/Enriched/Basic.lean:14-31,62-78 and AlgebraicTopology/ModelCategory/CofibrantObjectHomotopy.lean:55-95; none asserts the node. For the item also ran separate LeanFinder/LeanSearch queries for cofibrant-fibrant derived mapping complexes. Original recorded searches remain untouched.

Exploratory searches for the smaller complex pullback fact found model-category base-change stability (Mathlib/AlgebraicTopology/ModelCategory/Instances.lean:150-167, read); this alone does not state the dg-square and marked enhanced-localization result, so it is not a Mathlib match for the new node. The complex calculation is a future part of splitting that node, not a second unsearched new node. The unsuccessful Loogle query HomologicalComplex.QuasiIso, CategoryTheory.Mono reported an unknown identifier, not evidence of absence; it was not recorded as a completed absence search for either delivered node.

Whole-DAG keyword searches and blueprint_refs.py searches for quasi-equivalence, surjective quasi-isomorphism, resolution, replacement, commuting square, enriched localization and trivial fibration found no exact node. The apparent bounded-flat-replacement hit is about ringed-site complexes, not dg arrow categories. The new node has no Stacks tag shared with another node.

Small cases checked: the zero dg category and the identity resolution s=1 have the asserted projection; empty D forces S empty and gives the empty equivalence. For a single-object dg algebra the assertion is conditional on its explicit local surjectivity hypothesis, not on a false claim that all square projections are quasi-isomorphisms. Non-surjective quasi-isomorphisms are excluded: they would not generally allow the cycle-lifting argument. W need not satisfy two-out-of-three for this auxiliary lemma because it is detected by the projection; two-out-of-three is separately present in the item where it compares the two components. The dual statement has the correct map A(e_s,e_t) to A(d_s,e_t), by precomposition with s.

## Not duplicates

lem-coef-dg-resolution-square-projection vs lem-coef-dgcat-model-structure: the existing node characterizes dg trivial fibrations; it does not establish that the strict commuting-square pullback construction is such a map, or identify localization at markings pulled back from its projection.
lem-coef-dg-resolution-square-projection vs lem-coef-dg-quasifunctor-invariance: the existing node applies to an already proved quasi-equivalence; the new node establishes it for an arrow collection from the stated complex hypotheses and handles its marked localization.
lem-coef-dg-resolution-square-projection vs lem-coef-dg-model-mapping-comparison: the auxiliary lemma has arbitrary dg subcategories and arrow collections with local surjective quasi-isomorphism hypotheses, with no model category, bifibrancy, mixed Hom comparison or replacement independence. The item verifies these hypotheses and proves all its substantive model-specific conclusions itself.

## Review by Q11

I read the chapter and unit records, the three-level route rules, GOAL.md and dag-sync.md, and sections B through E of delivery-errors.md. I read the old blueprint source prop-coef-integral-exceptional-adjoint and its current main-20261015 proof file; paragraph 2 is the same coefficient mapping argument. It does not contain the new abstract foundation, so I retained agent provenance. The new lemma was checked against the explicit old steps 3 and 5, not attributed to a nonexistent Stacks theorem.

For step 1 I opened lem-coef-brown-split-factorizations: it supplies exactly both split factorizations used. The item itself supplies two-out-of-three and the enriched mapping axiom; the argument verifies cofibrancy/fibrancy of the middle objects. Its zero-Hom assertion uses the tensor/cotensor adjunctions explicitly. Step 2 is the actual pullback dg construction, with relation and composition written out; its weak equivalences are detected by the base component.

For steps 3 and 4 I checked the complete new projection statement. The postcomposition hypothesis is the mapping axiom applied to P and p', and the coverage hypothesis is the factorization of 0 to X. The restriction to cofibrant X retains both hypotheses. Step 4 retains the two inverse-comparison equations; lem-coef-enhanced-localization-universal explicitly carries transformations and their diagrams, so inverting the weak-equivalence components is justified.

For steps 5 and 6 I checked the dual clause of the new node: precomposition with j maps H(I,I') to H(X,I'), exactly the required direction, and I' is fibrant. When D=M_c, I remains cofibrant because j is a cofibration. When the source restriction is E, the same factorization produces a fibrant target still in D, verifying coverage rather than presupposing a model structure on a full subcategory. The maps k, a, pi and the natural transformation j give both inverse equations just as in the original proof. The generic projection node is strictly smaller than the item and does not assume any of these inclusion equivalences.

For step 7 I read lem-coef-derived-enriched-yoneda's definition of quasi-equivalence and derived enrichment. H^0 invertibility is proved here by the two explicit Hom quasi-isomorphisms from step 1. The localization node says localization has no effect when every enhanced functor already inverts the marked maps. For step 8 I checked that J and R are bifibrant, that both mapping-axiom arrows have the asserted variance, and that the canonical comparison from the single localization functor gives the naturality and composition diagrams. Pointwise equivalence implies equivalence of the enhanced transformation by the last clause of the localization node, now explicitly cited in this step.

For steps 9 through 11 I read the multivariable, diagram and contractible-extension clauses of lem-coef-enhanced-localization-universal, and the full pre/postcomposition invariance statement of lem-coef-dg-quasifunctor-invariance. Those statements provide precisely the hidden coherent-diagram lemma from old step 8. Ordinary functorial replacements yield only strict degree-zero diagrams, which are linearized before invoking enriched functors; the proof never treats them as enriched replacements. Enhanced diagrams lift through the actual projection equivalences with specified comparison, whose fibers are contractible. The final comparison of choices is made through the same mapping bifunctor, so it retains its specified coherence and composition.

I checked every proof use against the full cited statement and generated citations.json with verbatim excerpts, including the new node's two orientations. Definitions supply conventions, not unstated theorems. Reviewed B1-B10 for statement-only form, self-containment, TeX, source accuracy, real logged searches, blueprint ancestry and lack of an attachment; C1-C8 for explicit non-elementary citations, correct hypotheses, absence of reverse dependencies and route fidelity; D1-D5 for a genuine smaller auxiliary lemma and a complete item argument; E1-E7 for all local hypotheses, variances, zero/empty cases and coherent comparisons. No new definition, axiom, Lean file or compile was introduced. The only correction beyond the requested extraction is making the localization citation explicit at step 8, where the old proof already used its componentwise-equivalence assertion.

## Unfinished work

None for this stage-1 item. The new auxiliary statement is intentionally unsplit, as required for a one-level split.
