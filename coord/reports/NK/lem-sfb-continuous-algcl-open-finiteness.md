# lem-sfb-continuous-algcl-open-finiteness

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-algcl-open-finiteness.json: existing statement, split into five steps; statement and hypotheses unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-algcl-stratified-finite-models.json: new statement-only input, unsplit, no Mathlib match. Models on individual scheme strata over finite coefficient fields; it asserts no direct-image theorem.
- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-algcl-open-scalar-comparison.json: new statement-only input, unsplit, no Mathlib match. Invertibility of the specified coefficient-change mate on finite-field constructible inputs; it asserts no boundedness or constructibility of a direct image.
- citations.json: one verbatim quotation of the cited statement for each step/node pair.

The sandbox was initially empty apart from dispatcher brief markers; there was no earlier split or report to discard. All searches were run with the required msearch.py and their actual results are in searches.jsonl. The new nodes record only searches from that log; both phrasings of the coefficient-comparison query and both stratified-model queries were read. The service calls succeeded. The hits concern ordinary sheaf pushforward, free sheaves, constant condensed objects, fields and finite-type schemes, not these statements. The underived SheafOfModules.pushforward source was read at Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean:41-49. No search result is being declared a leaf.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, continuousMapRingObj, and continuous/algebraic-closure direct-image terminology. ProperLowerStarEllAdic contains proper-image assertions, not open-image finiteness. Its algebraic-closure coefficient is the finite-subextension-valued ring. The IntegralModel compact-representation theorem is useful evidence for the stratified-model input, but it states neither this item nor the new sheaf-descent statement. No sorry declaration is treated as an attachment.

## WANTED

WANTED: a published coefficient-change theorem proving invertibility of the ordinary open-image mate for the INCOMPLETE, norm-topologized algebraic closure with ALL continuous sections, for lem-sfb-continuous-algcl-open-scalar-comparison. The current blueprint calls for this compatibility case but does not prove this coefficient-specific exchange. Bhatt--Scholze's filtered-union argument is not such a theorem.

WANTED: a source stating finite-field models on strata for lisse modules over the all-continuous norm-topologized algebraic closure, for lem-sfb-continuous-algcl-stratified-finite-models. The expected argument passes to normal strata and descends compact matrix monodromy. The new node deliberately states the needed geometric coefficient-model assertion rather than pretending that the compact-group matrix theorem alone proves it.

These are statement-only obligations for the next level of stage 1; this delivery does not claim their proofs. The item's proof_origin is agent, and their source entries explicitly identify the agent-stated inputs required by the blueprint compatibility case.

## Source and import issues

No statement correction or route departure. Read GOAL.md, SETUP.md's three levels, the current main-20261015 chapter and unit, the unit record (which still contains the older snapshot), the current direct-images proof paragraph (3), and the open-coefficients proof. The current paragraph (3) proves finite-subextension rational finiteness through finite extensions, but the parent retains a separate all-continuous obligation. We retain that distinction and do not transfer a filtered-union theorem to the continuous ring.

Read Bhatt--Scholze, The pro-etale topology for schemes, sections 6.8 and 7.1, especially Example 7.1.7: the colimit topology and the extended absolute-value topology differ. Read Hemo--Richarz--Scholbach, Constructible sheaves, Theorem 4.13, Theorem 6.2 and the surrounding scalar-model discussion for the local-perfect calculation. The latter is used through an existing generic DAG statement, not as a finiteness theorem for the new open scalar-comparison node. No prohibited SGA source is used.

The imported blueprint ancestry ends at the parent's created.item Lean module name. The required blueprint_refs ancestor command therefore returns None. As in the reviewed parent and existing generator node, null from.node is retained, and from.place explicitly identifies det-thm-sf-ctf-stability-direct-images paragraph (3); the new via lists prepend this item to its parent's chain.

## Not duplicates

lem-sfb-continuous-algcl-stratified-finite-models vs lem-sfb-lisse-finite-coefficient-model: the existing node uses the finite-subextension-valued condensed ring; the new node uses all norm-continuous functions and asks for finite-field models only after stratification.

lem-sfb-continuous-algcl-stratified-finite-models vs lem-sfb-continuous-qbar-constructible-generators: the existing node gives finite-cone generation by all-continuous lisse sheaves; it gives no finite coefficient fields. Its generator theorem is cited, not recreated.

lem-sfb-continuous-algcl-stratified-finite-models vs lem-real-compact-matrix-coefficient-descent: the existing statement concerns representations of a supplied compact group, not module sheaves or scheme strata. It does not supply the geometric monodromy realization/descent needed here.

lem-sfb-continuous-algcl-open-scalar-comparison vs lem-sfb-qlbar-direct-image-comparison: the existing comparison has the filtered-union algebraic-closure ring as target; the new target coefficient has all continuous functions. No coefficient-ring isomorphism is asserted.

lem-sfb-continuous-algcl-open-scalar-comparison vs lem-sfb-rational-open-direct-image-constructible: the existing statement proves bounded constructibility for finite E and for the filtered-union algebraic closure. It neither states the all-continuous exchange map nor its invertibility.

lem-sfb-continuous-algcl-open-scalar-comparison vs lem-sfb-localized-direct-image-comparison: the latter inverts ell in a finite coefficient field's valuation ring; the new map extends that finite field to the norm-topologized algebraic closure. These are different scalar changes.

Searched the whole DAG by all-continuous, compact monodromy, normal strata, finite coefficient models and scalar/direct-image comparison. Ran blueprint_refs searches for continuous algebraic, coefficient descent, compact subgroup, normal stratification, scalar extension direct image, stratified generators, topological field, continuous scalar, lisse finite, open scalar, finite models strata and norm topology. No blueprint node states either new input. No Stacks tag is assigned to the two new coefficient-specific assertions, so there are no same-tag pairs to distinguish.

## What remains

The two new nodes require their own later splits. There is no Lean work, compiler invocation, global build or repository edit in this stage-1 delivery. The item is a complete reduction to those strictly different inputs and the existing DAG. It is not a claim that every branch below it is already proved.

## Review by NK

I checked delivery-errors B--E against the actual statements and sources. Both new statements introduce the base, coefficients, topology, module category and finiteness predicates. They contain no proof sketches, proof steps or proof dependencies. The comparison node defines the actual mate using the counit and pullback/tensor isomorphism. Thus it does not merely postulate an unspecified isomorphism, and it cannot be replaced by the filtered-colimit coefficient comparison.

Step 1 uses the Noetherian finite-type theorem over Spec(k), qcqs over an affine, and the all-continuous generator statement. I read that statement: it gives BOTH finite-cone generation and triangulated closure of precisely bounded finite-constant-model complexes. The total-derived definition identifies the bounded-below version; the generic bounded-below triangulated theorem, rather than just the definition of direct image, supplies preservation of triangles. Every generator and finite construction used is bounded below, so no unbounded comparison is inferred from that theorem.

Step 2 uses the new finite-model statement only for models on individual source strata. The good-stratification statement gives a finite closure-compatible partition. I corrected a possible scheme-structure error by realizing refinements inside each original scheme stratum through pullbacks, so the finite-field models genuinely restrict along scheme morphisms. The open/closed module theorem gives the exact sequence with precisely these restrictions and exact extension functors. Induction on the number of strata gives the finite filtration; it uses no non-small colimit and no global finite-field descent of the original sheaf. I retained a_!b_! as two successive exact extensions, avoiding an uncited identification of locally closed extension functors.

Step 3 uses the immersion-extension statement to keep the finite-E sheaf constructible at both successive immersions. The field case of the finite-flat-resolution statement identifies the scalar models with finite free modules. I checked the two support projection formulas: both are stated for arbitrary complexes and any condensed coefficient, so B restricted to an A_E-module is permitted. Applying them to the open and closed factors of a and b gives the scalar comparison. Its maps are linear for B because they retain the same local scalar multiplication; restriction of coefficients alone is not being mistaken for an isomorphism of B-modules.

Step 4 uses the finite truncation triangles, stability and local-perfect characterization of dualizable objects, and the actual derived tensor/pullback comparison. On each stratum finitely many lisse cohomology sheaves form M by the bounded Postnikov filtration, hence M is dualizable there. On pro-etale covers its perfect scalar E complexes are extended termwise to Omega. Over a field these finite complexes split as cohomology and contractible summands, so the resulting cohomology has the same interval and finite scalar models. Nonempty cover members detect the scalar interval, since the nonzero coefficient field embeds in its regular sheaf; empty members may be discarded. The open/closed exact sequence detects vanishing across strata. This is a written calculation from the cited statements, not a claim of exact scalar extension on arbitrary ambient modules. The step is 1599 characters, and none of the five steps exceeds 2000 characters.

Step 5 applies only the finite-E clause of rational-open finiteness. Its hypotheses are all present: separated finite-type schemes over the given positive-characteristic field, ell invertible, qc open j, and bounded constructible C. The new comparison statement gives exactly the coefficient-linear mate needed to identify its scalar extension with the B-coefficient direct image of G. The finite triangle closures from steps 1--2 then give the full item; no Tor, proper-image or compactification assertion has slipped into the conclusion.

I tested empty schemes, empty and identity opens, zero sheaves, zero rank, disconnected finite stratifications and constant finite-free models. Stratified models take E=Q_ell in rank zero; they do not demand a global field or a globally lisse lattice. The comparison is the identity for j=id and is the zero-object isomorphism for empty U; constant models on G_m in A^1 give the expected finite-field scalar-extension comparison. I also tested the forbidden shortcut: on the convergent profinite sequence N union {infinity}, choose algebraic alpha_n outside an increasing exhaustive chain of finite extensions, multiply them by sufficiently large ell powers so they tend to zero, and send infinity to zero. This is a continuous Omega-valued function not contained in any one finite extension. Neither new node asserts that all such sections have a finite field of definition. This confirms why the new exchange input is essential and why the finite-subextension theorem cannot be cited for it.

I regenerated citations.json after reading every used node's current statement. Quotations retain their complete wording to avoid hiding hypotheses; every quote is an exact substring of that statement. Generic off-unit scalar and derived tools are declared in split_report.tool_uses for maintainer review. The unit route remains finite-E open finiteness plus a distinct coefficient compatibility step. The dry run and push result are supplied by the delivery tool.
