# Stage-1 delivery: lem-sfb-smooth-presentation-closed-subsets

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-presentation-closed-subsets.json: item split into seven steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-invariant-closed-substack-descent.json: new statement-only lemma, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-smooth-reduced-locality.json: new statement-only lemma, unsplit, no Mathlib match.
- citations.json: twelve citation occurrences, each backed by the cited statement verbatim.

## Attachments

None. Searched the project WeilConjectures source by blueprint id, algebraic-stack names, closed-substack names and the relevant notions. The existing scheme smoothness/reducedness declarations do not state this item for algebraic stacks. No compiler or Lean-writing tool was used.

## Wanted

None: the proofs used are present in the local Stacks source. No SGA source is used.

## Corrections and scope

Replaced the item's algebraic-stack definition citation to def-sfb-adequate-moduli-space with def-sfb-algebraic-moduli-stack. The former defines a special kind of moduli morphism, rather than the algebraic-stack notion. The mathematical hypotheses and every conclusion are retained. The closed substack is understood as strictly full (closed under isomorphism), as in Stacks 04YM and the new closed-descent node. Uniqueness is of the substack, not of its chosen chart.

The inherited blueprint.from.node is null; blueprint_refs.py ancestor returns None. This is inherited nonimported ancestry, not a missing proposed blueprint id. Retained that ancestry and its full via chain; the new nodes add this item to that chain. Read the current latest blueprint sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3); the current high-level proper-direct-image route is shorter than the historic expanded ancestry. This delivery supplies the generic stack-topology prerequisite of the existing affine-PGL quotient item and does not change that route. The item is not a unit key node; no realization record was edited.

## Searches and reuse

Read the actual msearch output for each query recorded in the JSON and the searches.jsonl log. Both new nodes have two differently phrased semantic searches, Loogle, Mathlib grep and LeanSearch; the item was also searched anew. Scheme closed-immersion descent does not construct a closed substack from an invariant closed subscheme. Smoothness of reduced group schemes is the reverse implication and requires a group over a field; I read Mathlib/AlgebraicGeometry/Group/Smooth.lean lines 30--76. Scheme open-immersion reducedness and smooth-over-field results do not give the algebraic-space statement over a general reduced base. No new Mathlib leaf was found.

Searched the whole DAG by tags 04XH, 04XJ, 04XL, 0509, 0507, 034E, 0GB3 and key phrases; searched the blueprint with blueprint_refs.py for stack, invariant closed, reduced smooth, 0507 and 0GB3. Reused the existing point-topology, chartwise calculus, algebraic-stack fibre-product, and reduced-closed-space support nodes. The DM-only topology/open-substack node cannot supply the general Artin stack result. The existing invariant-open descent node does not descend closed scheme structures.

## Not duplicates

lem-sfb-invariant-closed-substack-descent vs lem-sfb-invariant-open-substack-descent: closed subschemes and equality of their scheme-theoretic pullbacks, rather than open subschemes; the existing node asserts only open-substack descent.
lem-sfb-invariant-closed-substack-descent vs lem-sfb-open-substack-unions: the latter constructs unions of open substacks, not closed substack structures from invariant ideals.
lem-sfb-space-smooth-reduced-locality vs lem-trf-etale-reduced-regular-center: the latter assumes locally Noetherian schemes and regular closed centers with etale local models; the new node is reducedness ascent/descent for smooth algebraic-space morphisms without Noetherian or regular hypotheses.
lem-sfb-space-smooth-reduced-locality vs sbc-lem-smooth-geometrically-reduced: the existing statement concerns geometric fibres of a scheme morphism, not reducedness of a total algebraic space over an arbitrary reduced base.

Neither new node repeats a clause of the item: the item concerns topological closed subsets and reduced closed substacks; the descent input concerns arbitrary, possibly nonreduced, closed subscheme structures with scheme-theoretic invariance, while the reducedness input has no stack quotient or closed subset. Both are independent general facts needed to prove the actual reduced-substack construction. Set-theoretic fibre-product surjectivity is proved directly rather than extracted as a new node.

## Review by Q27

I read Stacks stacks-properties.tex Tags 04XH (lemma-points-cartesian), 04XJ (lemma-points-presentation), 04XL (lemma-topology-points), and 0509 (lemma-reduced-closed-substack). For the closed-descent input I read 0507 (lemma-substacks-presentation), its closed-case assertion and factorization proof, and 04YN (lemma-immersion-presentation) with its cartesian square. For the reducedness input I read spaces-descent.tex 0GB3 (lemma-reduced-local-smooth), including both directions and its etale-chart reduction; I also read descent.tex 034E and spaces-properties.tex 03IQ. Corrected an initially mistyped source tag 04YL to the actual 04YN before the dry run.

Step 1 uses exactly the statement of lem-sfb-algebraic-stack-fibre-products to know that the explicit triple defines an algebraic stack; its statement gives the triple and comparison isomorphism. The remaining point lift is immediate from the definition of equality of point classes. I checked it requires common extensions of representatives, not K- and L-points over a fixed algebraically closed field, and proves surjectivity only. This also proves the image base-change assertion directly.

Step 2 cites the existing general stack-point-topology-flat-lfp-open statement for the quotient criterion, atlas independence, continuity and openness of flat locally presented maps. The chartwise-calculus statement explicitly says smooth implies flat and locally finitely presented, and surjectivity is field-extension local lifting. Thus its hypotheses apply to the atlas without a quasi-compactness assumption. Step 3 uses only step 1 and the defining equality q s = q t up to the specified 2-isomorphism. Step 4 uses the already-cited quotient criterion and proves saturation and the inverse operations as set equalities; these are elementary steps, not hidden new topology lemmas.

Step 5 cites lem-sfb-space-reduced-closed-support for both existence/uniqueness of the reduced closed subspace and the support of every closed base change. Its statement explicitly does NOT promise reducedness after arbitrary base change. I therefore obtain smoothness of the two projections and their pullbacks from chartwise calculus and apply the new smooth-reduced-locality statement. This supplies reducedness before applying uniqueness on R. R is an algebraic space, not silently a scheme. No assertion that every inverse image of a reduced closed subspace is reduced occurs.

Step 6 uses the closed-descent statement for exactly its invariant-closed correspondence, algebraicity and the atlas Z -> mathcal Z. The invariant equality was proved in step 5 as closed subspaces, not merely supports. For an arbitrary smooth chart W of mathcal Z, P=W times_mathcal Z Z is an algebraic space, smooth over the reduced Z and smooth surjective over W by chartwise calculus; the new reducedness node supplies ascent and descent in that order. Atlas point lifting gives the support calculation. Step 7 uses the existing reduced-support uniqueness for Z' in V and injectivity of the new closed-descent bijection. This fills the uniqueness proof omitted in 0509; it does not appeal to the proof of a cited node.

I tested the empty stack and empty atlas, the empty/full closed subset, the identity scheme atlas, a nonreduced scheme (the full subset produces its reduction, not the original scheme), and stacks with nontrivial stabilizers such as B G_m. The common-extension triple works with imperfect ground fields and needs no reducedness of stabilizers. The reducedness input requires smoothness: arbitrary inseparable base change need not preserve reducedness, consistent with the statement. Every new statement introduces its own base and spaces/stack, with inline reducedness and closed-substack meanings and definition dependencies. New nodes have no proof or proof dependencies. Each proof step has uses and an elementary verdict, the union is proof_deps, and every citation has been opened and copied into citations.json. No step is over 2000 characters. No replacement of an item clause by a renamed new node, unused document citation, unverified extra hypothesis, or SGA route remains.

## Unfinished work

Only the two intentionally statement-only inputs remain for subsequent stage-1 workers. This item's split and self-review are complete; delivery checks are run by the required server tools.
