# O4 repair: lem-pe-profinite-sections-finite-quotient

## Files written

- dag/nodes/sec-proetale-coefficients/lem-pe-profinite-sections-finite-quotient.json: unchanged statement; repaired assembly in six steps, 2931 characters. Only proof, proof_deps, proof_origin and split_report differ from the current read-clone parent.
- dag/nodes/sec-proetale-coefficients/lem-pe-internal-module-sectionwise-short-exact.json: one new statement-only lemma, status unsplit; no proof or proof dependencies, no exact Mathlib match.
- citations.json: literal current-statement excerpts for every node used by every parent proof step.
- report.md and extracted-argument.md: current review and the full argument assigned to the new node. The previous report and extracted-argument notes are preserved as report-before-current-repair.md and extracted-argument-before-current-repair.md. Earlier withdrawn attempts remain in retired-resplit-20261021/. Their routes are not part of this delivery.

One new node, zero Mathlib leaves. No Lean, repository or launcher file was written; no compiler, Lake, local checker or other agent was run.

## Attachments

No new attachment. The parent already records Profinite.continuousSections_finiteDiscrete_shortExact in lean/Sheaf/Topology/ProfiniteSectionsFiniteQuotient.lean:175. I read the completed proof and preserved its lean, reviewed_lean and reviewed_proof records. The explicit human instruction of 2026-10-21 renews this stage-1 re-split despite the completed Lean, so this is a natural-language extraction, not a claim that the existing Lean still contains sorry. No project declaration under WeilConjectures states the new general internal-module criterion. The private sectionsLinear and sectionsMap constructions are not additional attachments of the complete parent.

## WANTED

None. The source blueprint, current Lean and all cited DAG statements are available locally. No SGA source is used.

## What was repaired

L returned the side completion because it had not been promoted to the live DAG used by the queue. I continued the retained sandbox rather than restarting. Its first required dry run exited successfully at 2b532669220, with OK (not pushed). I then rebuilt the parent from the current read-clone JSON, copying back only the four split-owned fields. Thus the statement, chapter/unit, creation record, blueprint, imported fields and all completed Lean/review metadata are current and unchanged. Delivery builds and checks its commit on the current server DAG; no git command was run in the read clone.

This is a content repair, not an unchanged re-push. The current parent keeps pointwise module construction, injectivity and zero composite, continuous division through the topological kernel, discrete value lifting, and construction of the internal arrows. Its final passage from evaluated abelian groups through presheaves and sheafification to internal modules is isolated as the new general lemma. Step 1 explicitly checks continuous scalar multiplication and the module axioms by evaluation. Step 5 explicitly cites the sheafification adjunction, tests equality on pure tensors, and writes the action-compatibility formula. Step 6 states the site/coefficient universes. Every argument in the current live proof remains either in the assembly or in the extracted lemma's obligations and the full argument below; no argument was replaced by a vague assertion of transport.

I compared current and retained statements of every citation and reread them, including the new child's four statement dependencies. The current tensor definition states the sheafified objectwise tensor and its universal setting; the module-object definition states the exact action-compatibility equation; the continuous-section-module definition specifies the existing restricted regular module and its sections/action; the sheafification definition states unique factorization to a sheaf. None of these changed in a way requiring a different route. The old equivalence-based proposal is withdrawn and is not submitted. I corrected extracted-argument.md, which still described that obsolete proposal; its previous contents are preserved separately.

## Sources and Mathlib searches

I read GOAL.md, the requirements and three blueprint levels in SETUP.md, the worker/stage-1 contract, delivery-errors B through E, the chapter sec-proetale-coefficients and unit sk-lem-pe-derived-nakayama. The item's source is literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-resolution.proof.md, On the point and Triangles. Its continuous division, discrete lifting and final condensed-exactness assertion are the route followed. The new lemma makes that last assertion precise on an arbitrary essentially small site. Its source is the same paragraph, elaborated by the actual landed Lean argument at lines 286--332; this is agent-written elaboration, not a claimed Stacks theorem. No source statement or target statement was corrected.

Before changing the extraction I read searches.jsonl and all seven recorded searches for the unchanged new lemma. They are three grep searches, two LeanFinder phrasings, one Loogle and one LeanSearch. Every query in the child's mathlib_searches occurs verbatim in that retained log with its actual results. No search was invented or repeated. The earlier searches for the withdrawn comparison are not evidence for this new statement.

I read the candidate results and opened Mathlib/CategoryTheory/Abelian/ShortExact.lean:30, Mathlib/CategoryTheory/Monoidal/Mod.lean:347, project WeilConjectures/Mathlib/Algebra/Homology/ShortComplex/Exact.lean:26, and WeilConjectures/CategoryTheory/Monoidal/Mod/Abelian.lean. Faithful reflection is already Mathlib, but only supplies the last operation. MayerVietorisSquare.shortComplex_shortExact concerns one particular sheaf complex; homological-complex evaluation has another category; SheafOfModules.instAbelian uses a different module encoding. The internal-module abelian theorem and the presheaf/sheaf passage are additional ingredients, so the full criterion is not a one-line specialization of a hit. The child remains unsplit.

I searched the entire DAG and blueprint by sectionwise short exactness, internal modules and the criterion's notions, and checked blueprint_refs.py ancestor. The nearest ancestor is det-pe-derived-nakayama-resolution. Neither a blueprint node nor a current project declaration states the new criterion. The child's from.place identifies the final On the point assertion and via contains the parent. All seven original searches and their verdicts are retained; no new mathematical statement or search question was introduced by this repair.

## Full argument assigned to the new statement-only node

Forget the prescribed internal module sequence to abelian sheaves and then to abelian presheaves. Kernels and cokernels of abelian presheaves are computed objectwise; the assumed short exactness at every evaluation therefore gives presheaf short exactness, including both end conditions. Exact abelian sheafification gives a short exact sequence of sheaves. The natural sheafification isomorphism identifies the terms AND arrows with the original underlying sheaf sequence. The sheafified tensor is additive and closed, hence tensoring with the ring object preserves finite colimits. The internal-module category is consequently abelian. Its forgetful functor to abelian sheaves is faithful and preserves zero morphisms, so Mathlib's faithful reflection of short exactness gives internal short exactness with the original arrows. These are several categorical arguments with distinct hypotheses, not a two-line elementary observation. The node itself contains no proof sketch, proof steps or proof dependencies.

## Not duplicates

lem-pe-internal-module-sectionwise-short-exact vs lem-pe-profinite-sections-finite-quotient: the parent proves evaluated exactness for continuous functions on topological rings and constructs the internal arrows; the new criterion assumes evaluated exactness of arbitrary internal modules on any essentially small site and proves the categorical passage. It does not restate the parent's first conclusion, its full statement or its arrow construction.

lem-pe-internal-module-sectionwise-short-exact vs lem-weil-pbc-abelian-presheaves-evaluation-exact: the latter supplies the abelian presheaf category and objectwise kernel/cokernel formulas, not passage to sheaves and internal modules.

lem-pe-internal-module-sectionwise-short-exact vs lem-weil-pbc-sheafification-exact: exact sheafification is one ingredient; it does not establish internal-module exactness from evaluated groups.

lem-pe-internal-module-sectionwise-short-exact vs lem-weil-pbc-sheaf-tensor-closed: the latter supplies monoidal/exact-sheafification infrastructure, not this sequence criterion.

lem-pe-internal-module-sectionwise-short-exact vs lem-sfb-modobj-abelian: existence of an abelian internal-module category does not test a prescribed sequence.

lem-pe-internal-module-sectionwise-short-exact vs lem-sfb-modobj-forget-faithful: faithfulness is only the final ingredient, not the evaluated exactness criterion.

lem-pe-internal-module-sectionwise-short-exact vs lem-sfb-internal-module-operations-transport: that statement identifies functors for scheme sites through a module equivalence; this criterion works for arbitrary sites through sheafification and forgetting.

lem-pe-internal-module-sectionwise-short-exact vs lem-weil-pbc-jointly-reflect-short-exact: that result assumes exact functors jointly reflecting isomorphisms. Sheaf evaluation need not preserve epimorphisms; the new criterion proves a sufficient implication using presheaf evaluation and sheafification.

lem-pe-internal-module-sectionwise-short-exact vs lem-pe-internal-section-tensor-comparison: the latter compares relative tensors and exact module equivalences on ringed sites, not the evaluated short-exactness test.

## Review by O4

For step 1 I read def-sfb-continuous-sections-module. It specifies restriction of the regular module along the continuous scalar map, with exactly the sections, restrictions and pointwise action used. Its continuous-scalar hypothesis follows by composing the given scalar ring map with multiplication. The module axioms hold at each point. Composition is continuous, and the two displayed additivity/scalar identities show that F_S and G_S are C(S,A)-linear. I made the module-axiom verification explicit in this repair.

Step 2 has no non-elementary citation: evaluating equal images and applying injectivity of f gives injectivity of F_S; im f = ker g gives g(f(t))=0. Step 3 really uses the stipulated homeomorphism onto the subspace kernel. The explicit inverse-image identity proves that the kernel-valued section is continuous, and composition with the inverse homeomorphism gives a continuous preimage. Step 4 chooses a preimage for each quotient value and proves continuity by the union of open singleton fibers. No linear right inverse is asserted. All three arguments remain written in the parent, rather than being hidden in new nodes for elementary facts.

For step 5 I reread sk-def-sfb-sheaf-tensor, sk-def-sfb-module-objects, def-sfb-continuous-sections-module and def-weil-pbc-sheafification. Their statements respectively give the sheafified tensor, the morphism compatibility equation, the existing module action, and unique factorization through sheafification. They justify testing the two action maps on the objectwise tensor presheaf. Additive maps out of tensor products are determined on pure tensors, where the written identity f(alpha_0(a(s))u(s)) = alpha_1(a(s))f(u(s)) is A-linearity. Naturality is associativity of composition. The zero composite follows by evaluation and step 2. This never identifies sections of a sheafified tensor with the tensor product of sections. Every cited statement supplies precisely the fact used, and its literal quote is in citations.json.

Step 6 uses only the new criterion. I checked its statement explicitly assumes a short complex of internal modules and short exactness at every evaluated underlying abelian group, and concludes short exactness with those same arrows. Step 5 supplies the internal arrows and zero composite, while steps 2--4 supply the evaluated exactness. Profinite sets in universe u and coefficient groups in u+1 satisfy its relative essential-smallness hypothesis. I read the child's definition dependencies sk-def-sfb-sheaf-tensor, sk-def-sfb-ring-object, sk-def-sfb-module-objects and def-weil-pbc-exact-sequence: they define every special structure its statement uses. No citation relies on the proof of another node.

For the new node I checked zero modules, the zero ring object, identity short exact sequences, an empty site, and a site with only identity coverings. Its implication holds in these cases. It is deliberately sufficient, not an assertion that all sheaf epimorphisms are surjective on sections. No flatness of the ring object is needed: right exactness of tensor follows from closedness and suffices for the internal-module abelian theorem. For the parent I checked S empty, S a point, T2 = 0, and f the identity. The kernel homeomorphism cannot be replaced by algebraic exactness: the identity from discrete Z_p to p-adic Z_p with T2 = 0 fails on continuous sections. That hypothesis stays. Finiteness stays even though the lifting argument only needs discreteness.

Against delivery-errors B--E: the child is self-contained and statement-only; every special notion has its definition dependency; search records have actual logged queries; no new definition duplicates the existing restricted regular module; the new lemma is neither the whole item nor a disguised copy of its sectionwise clause; no mathematical statement was weakened; every non-elementary parent use has a matching statement quote; every retained argument is present in the parent or the full extracted argument above; no cycle or alternate unit route is introduced. Generic tool uses are declared in split_report without changing the maintainer's tool_uses. The complete proof is 2931 characters and every non-elementary step is below 2000. The current parent statement and all non-split metadata are retained, including the completed proof record.

## Unfinished work and validation

The one new node is intentionally unsplit so its proof can be assigned separately. There is no unresolved source dispute or missing material. The completed parent Lean is preserved under the explicit human re-split instruction. I checked citation coverage and literal quote inclusion against the current DAG and sandbox, and confirmed that only the four split-owned parent fields changed. The required final dry run and push validate the delivery on the current server state; earlier receipts are historical, not claimed as validation of subsequent edits.
