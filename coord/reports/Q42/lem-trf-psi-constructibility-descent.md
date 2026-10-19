# Stage-1 report: lem-trf-psi-constructibility-descent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-psi-constructibility-descent.json: item, statement, split into four steps; no exact Mathlib match.
- dag/nodes/sec-trace-formula/def-trf-coherent-topos.json: definition, unsplit, no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-coherent-conservative-reflection.json: statement, unsplit, no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-oriented-constructible-coherent.json: statement, unsplit, no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-proper-base-change-coherent-conservative.json: statement, unsplit, no exact Mathlib match.
- citations.json: verbatim statement extracts for every node used in every step.

## Attachments

None. Searched the exact blueprint tag and vanishing-topos/oriented-product/nearby-cycle terminology under WeilConjectures in slopmaster2. No declaration states this result. Ordinary scheme constructibility and base-change theorems do not have the right topoi. Master was read only as reference material; no master sorry is treated as a proof.

## Wanted literature

WANTED: Fabrice Orgogozo, Modifications et cycles proches sur une base générale, author draft, sections 8.1 and 9.1, particularly Lemma 9.1.5, for lem-trf-psi-constructibility-descent and all four new nodes. The item already identifies the author-hosted PDF; I read printed pp. 17–18 and 21 online. No local copy was found in literature/. No document was downloaded. The item's proof_origin is therefore agent, with the online source and its location recorded, as required for unarchived literature.

## Problems found and corrections

The imported statement is correct and unchanged. The proof was absent. Orgogozo's Lemma 9.1.5 is a result about arbitrary sheaves, not merely nearby-cycle cohomology; consequently no Psi-goodness, invertibility of the ring order, finite Tor dimension or nearby-cycle comparison is needed here. His proof uses a coherent conservative geometric morphism and the equivalence of constructibility and coherence. These properties are not assertions of the existing oriented-product definition or its universal property. I made them actual statement nodes instead of citing a definition for theorems it does not state.

The finite-module criterion uses coherence of the underlying SET sheaf, not quasicoherence of a module sheaf and not the coherent SITE sheaf condition in Mathlib. Finiteness of the coefficient ring matters: finite module operations on a finite local set can be made constant by finitely many refinements. I retained the finite coefficient hypothesis in the new comparison statement.

The first draft misidentified base-change stability of finite presentation as 01TQ; the local tags table and morphisms.tex show the correct tag is 01TS, label lemma-base-change-finite-presentation, and the node was corrected before delivery. 01T6 is lemma-finite-type-noetherian. No SGA source is cited.

## Unfinished work

No part of this one-level split remains unfinished. Four new nodes remain unsplit intentionally; none carries a proof or proof dependencies. No Lean file was written, and no compiler, Lake or build tool was run. This item is not the unit's key node, so the unit realization file was not changed.

## Not duplicates

- def-trf-coherent-topos vs lem-trf-oriented-affine-slice-site: the former defines intrinsic coherence of arbitrary topos objects and morphisms; the latter constructs a site for one affine slice and states neither these definitions nor reflection of coherence.
- lem-trf-coherent-conservative-reflection vs lem-trf-oriented-affine-slice-site: general inverse-image detection of coherent objects is not a slice-site existence theorem.
- lem-trf-oriented-constructible-coherent vs def-trf-oriented-constructible-sheaf: the existing node defines finite product stratifications; it does not characterize their sheaves as intrinsic coherent objects.
- lem-trf-proper-base-change-coherent-conservative vs lem-trf-psi-constructibility-descent: the new result is structural geometry of topoi and involves no sheaf F or constructibility implication. It supplies a genuine hypothesis of the general reflection theorem, not a renamed descent assertion.
- lem-trf-oriented-constructible-coherent vs lem-trf-psi-constructibility-descent: the new criterion has no base-change map and makes no descent assertion. It is a comparison between two independent finiteness predicates.
- lem-trf-proper-base-change-coherent-conservative vs lem-trf-oriented-affine-slice-site: coherence and conservativity of the whole proper-base-change morphism, including point lifting, are not implied by the existence of a finite site for each affine slice.

Whole-DAG statement searches for coherent topoi, coherent objects and coherent geometric morphisms found only the affine-slice node and unrelated pro-etale-site or algebraic coherent-module facts. Blueprint searches used coherent topos, constructible coherent, proper surjective, vanishing, conservative and oriented terminology across all chapters. No blueprint node states a new child. The item's nearest blueprint ancestor is lem-trf-local-term-locality; every child records it with the item prepended to the inherited via list. The broad 'coherent' blueprint matches were coherent O_X-modules or coherence of diagrams, not intrinsic topos coherence.

- lem-trf-proper-base-change-coherent-conservative vs lem-sbc-composite-fibre-local-models: shared scheme permanence tag(s) 01T6 supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs pqf-def-locnoeth: shared scheme permanence tag(s) 01T6 supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs lem-nagata-qc-open-basechanged-affine-chart-fp: shared scheme permanence tag(s) 01TS supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs lem-pc-proper-base-change: shared scheme permanence tag(s) 01TS supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs pqf-lem-locnoeth-lft: shared scheme permanence tag(s) 01T6 supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs lem-weil-pbc-qcqs-morphism-permanence: shared scheme permanence tag(s) 01TS supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs lem-weil-pbc-finite-type-over-noetherian: shared scheme permanence tag(s) 01T6 supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs lem-weil-pbc-finite-algebra-noetherian: shared scheme permanence tag(s) 01T6 supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs lem-weil-pbc-graded-finiteness-cohomology: shared scheme permanence tag(s) 01T6 supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.
- lem-trf-proper-base-change-coherent-conservative vs lem-pur-affine-line-support-geometry: shared scheme permanence tag(s) 01T6 supply preliminary Noetherian/base-change checks; the new node asserts coherence and conservativity of a morphism of vanishing topoi, which the existing statement does not assert.

## Review by Q42

I read coord/brief-stage1.md, stages/1-dag.md, the three levels in SETUP.md, delivery-errors B–E in full, coord/dag-sync.md, GOAL.md, the worker role, the trace-formula chapter and sk-i-curve-zero unit, and the item's blueprint ancestry. This split preserves the conditional constructibility input of the nearby-cycle specialization argument already selected below the unit; it does not change the contracting-correspondence route or a target statement.

For the item I read Orgogozo's author draft Lemma 9.1.5, printed p. 21. Its proof explicitly uses point lifting, coherence of the base-change morphism and the coherence/constructibility comparison from section 8.1. For def-trf-coherent-topos I read the quasi-compact/quasi-separated terminology in section 8.1, printed p. 17. For lem-trf-coherent-conservative-reflection I read the coherence detection assertion in that same paragraph. For lem-trf-oriented-constructible-coherent I read the comparison with constructibility on pp. 17–18 and checked that the definition being compared is the finite product-stratification definition of the existing def-trf-oriented-constructible-sheaf. For lem-trf-proper-base-change-coherent-conservative I read the point-lifting and coherence assertions in the proof of Lemma 9.1.5 and the coherent triple-site description in section 8.1. I also opened the exact local Stacks lemmas for the two elementary preliminary scheme conclusions. These primary sources, rather than a guessed proper-base-change cohomology theorem, determine the split.

Step 1 uses exactly the structural base-change node: I checked its statement includes the coherent source and target, coherence and conservativity of v, Noetherianness of T and finite presentation of f_T. The original item's hypotheses supply all its assumptions. Properness is necessary here; mere surjectivity of schemes is not substituted for coherent conservativity on the vanishing topos.

Step 2 uses the exact-inverse-image clause of def-trf-oriented-nearby-cycles and the new intrinsic-coherence criterion. I opened the definition, including its constant-Lambda convention: the inverse image has underlying set inverse image and transported module operations. Step 1 supplies the two geometric hypotheses for applying the criterion to f_T, while the given constructibility hypothesis supplies the forward implication. The coefficient ring is the same finite ring on both topoi. No passage to arbitrary condensed/adically complete coefficients occurs.

Step 3 uses the general coherent-conservative reflection node, whose statement quantifies over every object of the target topos. I checked the object's type is the underlying set sheaf A in E, and that coherence of its inverse image is already established, so the invocation is neither circular nor an assertion about F being locally free. Step 4 uses the reverse implication of the same intrinsic-coherence criterion on the original f. The node's statement really returns the finite-module stratification convention, not just finite stalks or a definition of a constructible subset. citations.json records verbatim text for every use, with a second local check that every quote is a substring of its node statement.

I checked B–E against the actual JSON files. The four children introduce all their objects and cite their notion dependencies. None carries a proof sketch. The general reflection lemma separates a topos theorem from geometric base change; the comparison lemma separates intrinsic coherence from scheme-stratified constructibility; the structural lemma does not assert descent. Thus the proof is not moved into a renamed clause of the item. Each theorem's dependency direction is downward through the coherence definition and existing definitions, never back to the item. No new child is an elementary restatement of one cited theorem. The item steps are all under 600 characters; none triggers the 2000-character hidden-lemma review.

For Mathlib I ran and read the logged LeanFinder, LeanSearch, Loogle and grep searches before creating nodes, using second concept phrasings. I opened CategoryTheory/Sites/Coherent/SequentialLimit.lean and Equivalence.lean: their sequential-epi theorem and sheaf-category equivalences do not give coherence of objects or its detection along an arbitrary coherent conservative geometric morphism. Returned IsQuasicoherent/IsFinitePresentation declarations concern presentations over a sheaf of rings, not intrinsic coherence of underlying sheaves of sets. Returned coherentTopology sheaf conditions assert that a presheaf is a sheaf, not that an object of a topos is coherent. The ordinary scheme isConstructible_image and proper base-change stability signatures do not mention vanishing topoi. No candidate is an exact match or a one-line specialization. The search records are copied from actual searches.jsonl entries, and no unavailable service is called a no-match.

Small cases: p the identity makes the structural morphism the identity and the descent conclusion tautological; S or X empty gives the degenerate topos and empty stratifications; a sheaf with zero module values is the one-element underlying set sheaf (not the empty sheaf) and satisfies both finiteness predicates; a constant finite module is constructible/coherent; an infinite discrete module on a geometric point fails both predicates. The generic reflection statement for identity topoi, and a surjective point cover of a coherent topos, has the correct implication direction. The empty-to-nonempty map is excluded by conservativity/proper surjectivity. These cases do not require ring-order invertibility.

The dry run and delivery results are recorded below after the required server checks.

## Validation

The required deliver.py --no-push invocation passed the server preflight and wrote the durable .stage1-ready.json receipt. All citation and search-log checks passed. The final report is included in the final dry run and push.
