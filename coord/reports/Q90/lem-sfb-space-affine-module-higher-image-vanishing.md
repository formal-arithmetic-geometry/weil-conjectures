# Stage-1 report: lem-sfb-space-affine-module-higher-image-vanishing

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-module-higher-image-vanishing.json: item, statement, split, no Mathlib match. Five proof steps, using existing nodes only.
- citations.json: one verbatim statement quotation for every node used by every step.
- report.md: this report. Search outputs and searches.jsonl retain the actual searches and results.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for affine higher-image/acyclicity and module terminology. The scheme modules in AffineMorphismCohomologyEdge.lean and Cohomology/DirectImage/AffineMorphism.lean concern schemes and their Zariski modules; they do not state the item for algebraic spaces on the small etale ringed site. No compiler was run.

## Wanted literature

None.

## Audit findings and changes

The item's statement is retained verbatim: affine means representable with affine scheme base changes, coefficients are quasi-coherent structure-modules on the small etale ringed site, and right derived functors are computed in all module sheaves. It is different from the existing lem-sfb-space-affine-higher-direct-image-vanishing: that node concludes vanishing in abelian sheaves. Neither one is silently identified with the other.

I reused that existing additive result. The missing proof was the module/additive bridge, now written out via an actual injective module resolution, objectwise abelian acyclicity of its terms, the site formula for higher direct images, and the acyclic-resolution criterion. There is no new node that merely restates a clause. Forgetting a module injective need not preserve injectivity; the proof uses its abelian cohomology acyclicity instead. The general derived-direct-image comparison for constant ring coefficients on schemes does not supply the needed arbitrary structure-ring comparison, so it is not cited.

The inherited blueprint.from.node is null: blueprint_refs.py ancestor reports None for this created chain. I preserved that inherited field and the full from.place provenance rather than inventing a new ancestor. I read the current blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3), and its unit/chapter records. The current proof uses compactification and proper/open direct image. This prerequisite sits within the inherited proper-coherent input; its split does not replace any unit or chapter step. Whole-blueprint searches for affine vanishing, 073H, 03FD, higher direct images, and forget direct image found no blueprint node stating this module comparison or the exact item. The 03FD blueprint hit sk-def-pbc-conventions is a conventions node, not the theorem used here.

## Mathlib searches

Actual Q90 searches are in searches.jsonl and search-0.txt through search-6.txt; these exact queries and outputs were appended to the item's inherited searches. Both the item and its potentially generic comparison were searched with two natural-language phrasings, Loogle patterns and Mathlib grep. LeanSearch returned affineness of scheme morphisms; LeanFinder returned affine-scheme limit facts or underived SheafOfModules.pushforward and its formulas. I read Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean: its pushforward at lines 39 onward is underived. The other phrasing returned local injectivity and isZero_rightDerived_obj_injective_succ, which assumes the derived input is injective. Our quasi-coherent M is arbitrary, and the geometric acyclicity is not a one-line instance of that theorem. No hit proves the item. No unavailable service was relabeled as a no-match, and no unrun query was recorded.

## Not duplicates

No new nodes were created. The existing additive affine vanishing, ringed-site injective-module abelian acyclicity, chart-limit identification, exact scalar forgetting, Grothendieck category, and acyclic-resolution statements were all reused. A contemplated general comparison node was unnecessary: its argument is expressed directly in steps 1–4 using those statements.

## Review by Q90

I read spaces-cohomology.tex, Tag 073H (lemma-affine-vanishing-higher-direct-images), including its proof and the representable-higher-direct-image discussion near the start of that chapter. I also read sites-cohomology.tex, Tag 03FD (lemma-cohomology-modules-abelian-agree), statement and proof; Tag 072W (lemma-higher-direct-images), statement and proof; and Tag 0731 (lemma-limp-acyclic), to distinguish objectwise acyclicity from actual injectivity. There are no new nodes needing separate sources. This is the source's module/additive resolution argument, assembled with the already split additive geometric vanishing input.

Step 1 uses lem-weil-pbc-ring-sheaves-grothendieck, whose statement explicitly allows arbitrary ring sheaves on small sites in the coefficient universe, and lem-sp-grothendieck-enough-injectives, which then supplies the resolutions. The resolution definition is def-sp-injective-resolutions. Exactness of forgetting is clause (1) of lem-weil-pbc-module-sheaves-colimits-forgetful, not an assumption about flat coefficients. The abelian categories have enough injectives by lem-weil-pbc-site-sheaves-enough-injectives. I opened and read each of these statements. Small representative sites in a common larger universe meet their size hypotheses.

Step 2 uses lem-trf-space-chartwise-etale-permanence for base change of etale objects and coverings, lem-trf-space-enlarged-etale-ringed-site-model for the canonical continuous base-change presentation, and lem-trf-space-chart-limit-enlarged-sections for its agreement with the actual module direct image specified in the item. Each of those statements was read. Because a is representable, its fibre product with every scheme object T is a scheme, so the base-change functor restricts to the scheme small sites; it is not an unsupported functor taking values in spaces outside the site. In the chart category the scheme U_T itself is terminal before passing to the opposite diagram, so its module sections are the limit vertex. The same restrictions and differentials give the claimed equality after forgetting.

Step 3 uses lem-sc-injective-module-abelian-acyclic-zariski. Despite its name, its statement says an arbitrary ringed site, arbitrary object U, and any injective structure-module sheaf. It states exactly H^r(U,I_ab)=0 for r>0. The generic site formula lem-weil-pbc-site-higher-direct-image-sheafified-presheaf applies to the continuous functor of step 2 and says the higher direct image is the sheafification of these groups. def-weil-pbc-sheafification supplies the universal property, which identifies the sheafification of zero with zero. Thus every term is a_*,Ab-acyclic, without any injectivity claim after forgetting. All quoted formulas are in the cited statements.

Step 4 invokes precisely clause (2) of lemma-weil-pbc-leray-acyclicity, which states that a nonnegative exact augmented resolution by acyclic terms computes right derived functors. Step 1 provides enough injectives, and direct image is left exact as a sectionwise limit, so its hypotheses apply. The module higher image is the cohomology of a_*I by the definition in the item and def-sp-injective-resolutions. Exact forgetting is cited again, and lem-weil-pbc-exact-functor-complex-cohomology states the needed natural isomorphism between forgetting cohomology and cohomology after forgetting. This gives an identification of the actual sheaves. It does not assert a derived isomorphism without proving its comparison or create a node stated only degree by degree.

Step 5 reads lem-sfb-space-affine-higher-direct-image-vanishing literally: its map f:Y→X becomes a:V→W, its F becomes M, its hypotheses are representability/affine base changes and quasi-coherence on the same site. It has no Noetherian, properness, finite-type or coherence restriction. The last inference is explicit: faithful forgetting makes id=0 once the underlying object is zero. This is detection of the zero module, not an unjustified use of scalar-restriction injectivity.

I checked B1–B10: no new unsplit nodes, no artificial clauses, no incorrect Mathlib leaf or unrun search; statement and provenance fields retained. I checked C1–C8 against every cited node's statement and wrote verbatim citations for each; no proof-only content is taken from another node, and dependency closure inspection found no path from any cited node back to this item. Generic tools from other units are declared in split_report.tool_uses for maintainer review. I checked D1–D5: the steps contain the resolution argument, rather than moving the theorem into one new node or citing definitions for unproved non-elementary facts. I checked E1–E7: fibre products have the correct base W, each needed representability and coefficient-universe condition is available, and no structural-map flatness is used.

Edge cases: M=0 and empty source or target give zero; the identity affine morphism gives vanishing of its positive derived functors; q=0 is intentionally excluded, since a_*M can be nonzero (already for the identity and M=O). Arbitrary non-Noetherian affine bases and infinitely generated quasi-coherent M remain allowed. Thus none of the proof adds finite-presentation, coherence or finiteness assumptions. Every step is below 2000 characters, and the argument hides no unrecorded comparison: the site model, acyclic resolution theorem and exact-cohomology comparison are separate existing dependencies.

## Unfinished work

None in this stage-1 split. Downstream unsplit prerequisites retain their existing queue states; this delivery does not claim Lean proofs for them. Required server preflight and dry run follow this report.
