# Q120 stage-1 report: lem-zl-texact-fixed-pair-heart-cohomology

## Files written

- `dag/nodes/sec-deligne-laumon-general/lem-zl-texact-fixed-pair-heart-cohomology.json`: statement item, split into twelve steps; full package has no Mathlib match. Statement text unchanged. Added the explicit abelian-category definition and canonical heart/cohomology statement dependencies, normalized proof dependencies, source attribution, and tool-use declarations.
- `citations.json`: one verbatim statement excerpt for every citation in each numbered proof step.
- `report.md`: this report and signature.

New nodes: 0. New Mathlib leaves: 0. Sandbox-only supporting file: `write_split.py`; searches recorded by the mandated command in `searches.jsonl`.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and for fixed-pair/IsoAlgebra and t-exact terminology, and read the relevant project files. `CategoryTheory.Endofunctor.IsoAlgebra.abelian` in `WeilConjectures/Mathlib/CategoryTheory/Preadditive/EndoFunctor.lean` proves the abelian fixed-pair clause under exact additive endofunctor hypotheses, while `preservesFiniteLimits_mapOfNatIso` and `preservesFiniteColimits_mapOfNatIso` in `WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean` prove exact transport. Neither states the t-exact heart-valued cohomology comparison and its normalization/coherence, so there is no exact full attachment. I also read `IsoAlgebraHomology.lean`, `IsoAlgebraCompIso.lean`, `Shift.lean` and the declarations listed in `Triangulated/RecollementIsoAlgebra.lean`; those concern different comparisons. No compiler or Lake command was run.

## WANTED

None. BBD and the relevant project and Stacks source files are present.

## Audit findings and changes

The inherited item was unsplit, with an empty proof. Its hypotheses and conclusions are correct; no statement dispute or change is needed. Its source is explicitly an agent-extracted auxiliary package, rather than a theorem printed verbatim in the blueprint. I kept that distinction and marked the new proof as agent-written, based on the literature and explicit fixed-pair calculations.

The source blueprint is `main-20261015`, the proof of `lem-zl-morphism-open-closed-reduction`: the Restriction paragraph applies pullback to cohomology, and Part 2's sheaf form takes cohomology of the base-change comparisons using exact pullbacks. The chapter and unit records keep the open–closed reduction route; this item supplies its generic categorical justification and does not replace any geometric step.

A tempting existing statement, `lem-sf-fixed-pair-created-abelian-structure`, assumes all small limits and colimits in its underlying abelian category. The current item's hearts are not assumed complete or cocomplete. I did not apply that node or strengthen our hypotheses; instead Steps 8–11 give the finite universal-property constructions directly. This also avoids a new node merely restating a clause of this item. Existing project Lean was used as source material, not as a substitute for a DAG citation.

The seven fresh mandated msearch invocations (two semantic phrasings, Loogle, LeanSearch, and three grep queries) are recorded in the sandbox log. The broader grep pattern found many `shortExact` names, so I narrowed it to the triangulated directory and to `IsoAlgebra` in the endofunctor directory; both gave no hits. I inspected the truncation file and the exact-functor source behind the semantic hits. Homological functors, finite (co)limit preservation, and individual truncation isomorphisms are useful infrastructure but do not state this full equivariant t-exact package. Existing inherited searches remain intact. No search is fabricated and no unavailable service is counted as an absence result.

## Not duplicates

No new nodes were created. Whole-DAG searches by fixed-pair, t-exact/cohomology, kernel, abelian and truncation terminology, together with `blueprint_refs.py search` for `t-exact`, `fixed pair` and `cohomology comparison`, located the comparison, lifted Postnikov and heart nodes reused in the proof. The package itself was not found elsewhere. The nearby fixed-pair created-abelian statement is stronger in completeness hypotheses and covers only the abelian-structure part, while `lem-zl-texact-cohomology-boundary-comparison` concerns connecting morphisms without fixed pairs. Neither duplicates the current statement. The geometric `lem-pod-fixed-pair-truncation-cohomology` is not silently used as a generic theorem; its generic `lem-pod-fixed-pair-postnikov-identifications` dependency has the needed abstract hypotheses and formula.

## Unfinished work

No stage-1 proof step remains unfinished. The cited unsplit generic Postnikov node remains a separate existing queue item, not a new obligation disguised as a finished theorem here. No Lean statements or proofs were written.

## Review by Q120

I read delivery-errors sections B–E in full, the stage-1 brief and stage document, the worker role, GOAL, SETUP's three levels, and this chapter/unit and current blueprint proof. The mathematical sources read for the item were BBD Proposition 1.3.3 and paragraphs 1.3.4–1.3.5 (printed pp. 29–30), its heart/cohomology Theorem 1.3.6, and the t-exact definitions/proposition 1.3.16–1.3.17 (printed pp. 36–37). I read the project fixed-pair abelian and transport sources cited above. I read `literature/stacks-project/homology.tex`, `lemma-exact-functor` (Tag 010N, as identified by the existing exact-functor node), for the short-exact and finite-limit/colimit notion. BBD is used for abstract t-structures because Stacks' truncations of complexes do not state this abstract form. There are no new nodes needing further source review.

I opened and read the statement of every cited node: the fixed-pair definition, triangulated-category/exact-functor definition, canonical heart/truncation theorem, normalized t-exact truncation comparison, generic fixed-pair Postnikov identifications, exact-functor preservation theorem, and abelian-category definition. Their statements, rather than unpublished parts of their proofs, provide exactly the facts indicated below.

1. The fixed-pair definition gives the arrow condition and faithful forgetting. Substituting naturality of alpha proves the displayed arrow equation; invertibility and the functor laws are direct calculations.
2. The truncation-comparison node supplies both uniquely normalized isomorphisms. The heart/truncation node supplies heart-valued cohomology. I checked the cutoff order, the shift by +a, and the direction RH -> HR: the comparison requested by the item is its inverse. Preservation at all cutoffs follows from degree-zero preservation and the given shifts, not from boundedness alone.
3. The generic Postnikov node explicitly states the lifted truncation/shift functors and the formula H(theta)e_P. Its two-sided preservation assumptions hold for both P and Q and their inverses. It does not require a triangulated structure on pairs.
4. The truncation-comparison statement explicitly includes arbitrary natural-transformation compatibility and composition. Together with the given coherent shift comparisons from the triangulated/exact functor definition, these yield the two-factor shifted formula. The shift-compatibility condition on eta is used exactly where eta passes through s.
5. The fixed-pair definition identifies the displayed equation as the required one. I checked every source and target of the equation H(alpha)e_Q Q(e_F) = e_F F(e_P) alpha_H, then used naturality at theta. This supplies the actual intertwining proof, not a claim that equivariance transports automatically.
6. The two intertwiners compose as G(alpha) beta_F. I checked the equation for a natural isomorphism between intertwining functors explicitly, including compatibility with alpha, and used the identities already proved in Step 4 to obtain the cohomology square. Without that compatibility, an arbitrary natural isomorphism would not give an isomorphism on fixed pairs; the text spells out its precise meaning.
7. The heart theorem states both directions of the short-exact/distinguished-triangle criterion, and the exact-functor definition supplies preservation of distinguished triangles. All image terms lie in the target heart by t-exactness. Only then is the exact-functor-preserves-homology statement (a) applied, so its abelian/exact hypotheses have actually been proved.
8. That same statement (a) gives that P(k) is a kernel of P(u). The fixed-pair arrow equation gives both factorizations defining kappa and lambda. Cancelling the two kernel maps proves the inverse equations; cancelling k proves the equivariance of a universal factor h. Thus the uniqueness claimed is in the pair category, not merely on carriers.
9. I checked the dual argument independently: gamma P(q)=q theta_B, delta q=P(q) theta_B^{-1}. All factors exist because their composites with u or P(u) vanish. The two epimorphisms prove the inverse equations and equivariance of cokernel factors. There is no unsupported duality shortcut hiding a different orientation.
10. The abelian definition lists the needed preadditive, zero and biproduct requirements. The explicit biproduct structure and inverse multiply to the identity using only the four biproduct relations and P's additivity. Additivity is inherited from the triangulated restrictions, not an extra hypothesis.
11. The same definition requires normality. I checked reflection of monicity and epicity without assuming the desired abelianness in advance: created zero kernels/cokernels give ordinary zero kernels/cokernels, and the underlying abelian heart supplies normality. Cancellation proves the universal factors equivariant. In the epi argument P(u) is epi by the already justified exact-preservation node, so the cancellation is legitimate.
12. The exact-preservation node gives underlying kernel/cokernel maps for F. Naturality of alpha gives the two displayed equations for their transported structures, which are identified by the uniqueness proved in Steps 8–9. Created images and kernels detect exactness on carriers, and F is exact there. This proves exactness on pairs as well as preservation of the specified maps.

For small cases, P=Q=id and alpha=id recover objects with an invertible endomorphism and their usual invariant kernels/cokernels. On D^b of finite-dimensional vector spaces the hearts need not have arbitrary small products, confirming why the completeness-dependent lemma cannot be invoked. A zero functor F still satisfies the formulas and gives the exact zero functor of pair hearts. The zero category, u=0, and u=1 give respectively unique zero structures, the expected kernel/cokernel objects, and zero kernel/cokernel. For shifts and nonzero a, the formula H^a K=(tau^{>=a} tau^{<=a}K)[a] lands in degree zero, so the shift sign is correct. A nontrivial shift-compatible alpha remains in all equations rather than being identified with an identity.

No step exceeds 2000 characters; the longest is 1273. I checked that the short steps carry the actual arrow and universal-property arguments rather than hiding new lemmas. All non-elementary inputs are named existing nodes; elementary steps use the displayed formulas, definitions, and previous steps only. Every citation quote is verified as a literal substring of its node's statement. All changed files are in the assigned sandbox; no git command, repository write, agent delegation, compiler or build was used.
