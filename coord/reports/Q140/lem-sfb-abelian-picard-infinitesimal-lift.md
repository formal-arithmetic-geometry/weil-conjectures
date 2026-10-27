## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-picard-infinitesimal-lift.json: statement unchanged; split into five proof steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-picard-obstruction-natural.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-algebraically-trivial-line-multiplicativity.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-h2-reduced-coproduct-injective.json: statement, unsplit; no Mathlib match.

Three new nodes, zero Mathlib leaves. citations.json contains verbatim statements supporting every proof citation. searches.jsonl and sources/search-*.txt retain the actual searches and their complete answers. No Lean was written and no compiler or git command was run in the read clone.

## Attachments

None. The exact blueprint tag is absent from lean/WeilConjectures. Searches there for Picard infinitesimal lifting, rigidification, algebraically trivial lines, abelian schemes and coherent Hopf cohomology found only curve Picard statements, module pullbacks, or the field theorem of the cube. None states the relative algebraic-space lifting problem. Sorry declarations were not counted as attachments.

## WANTED

WANTED: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, Chapter 6, especially Proposition 6.7 and its preceding cohomological/group-law calculation, for lem-sfb-abelian-picard-infinitesimal-lift and lem-sfb-abelian-h2-reduced-coproduct-injective.

WANTED: the relative theorem-of-cube/Picard-kernel treatment in the same book, Chapter 6 section 2, for lem-sfb-algebraically-trivial-line-multiplicativity, including arbitrary parameter schemes and algebraic spaces. The field argument in Milne does not alone establish that relative assertion.

The worker cannot write literature/LIST.md or coord/HUMAN.md; this report records the requests for the maintainer. I did not obtain or pretend to read MFK. No SGA source is used. Bhatt's 2017 Abelian varieties lectures, sections 3.2 and 5.1, were checked online as orientation for the field multiplicativity calculation; the delivered proof does not rely on their dual-variety theorem.

## What was wrong or incomplete

The item was statement-only. Its source candidly distinguishes the field Milne reference from the unavailable relative infinitesimal-lifting reference. I retained that distinction. In particular I did not cite the parent lem-sfb-abelian-space-poincare-calculus: that parent's dual-space smoothness depends on this item and would create a cycle. No statement dispute or change of the unit route is needed.

The scheme node lem-sfb-square-zero-picard-obstruction is not sufficient for a step using algebraic spaces and pullback naturality: neither assertion appears in its statement. Its split proof cannot be borrowed as an extra public clause. The new functorial space obstruction states exactly what the computation uses, with Stacks Tag 0DNM rather than the scheme Tag 0C6R.

The ancestor command returns None for this created-node lineage. The inherited null from.node, the full from.place and the via chain are retained. The latest blueprint was searched, not an old snapshot. The unit is sk-thm-sf-ctf-stability; its realized fields are not this supporting node's to modify.

## Not duplicates

lem-sfb-space-picard-obstruction-natural vs lem-sfb-square-zero-picard-obstruction: the latter treats schemes and states exactness alone; the new node treats algebraic spaces and also states the coefficient-sensitive pullback equation for arbitrary squares of thickenings.
lem-sfb-space-picard-obstruction-natural vs lem-sfb-split-thickening-picard-cocycle: the latter is the H1 description of the kernel for the split dual-number thickening of a scheme over a field; the new node is an H2 obstruction and its naturality for arbitrary square-zero space thickenings.
lem-sfb-algebraically-trivial-line-multiplicativity vs lem-sfb-abelian-space-poincare-calculus: the parent constructs and proves smoothness of the dual space and gives Poincare biadditivity; the new node is only the group-law identity for one already given rigidified line, with no dual object or infinitesimal lifting conclusion.
lem-sfb-algebraically-trivial-line-multiplicativity vs lem-sfb-abelian-polarization-calculus: the latter gives the dual variety and polarization over algebraically closed fields; the new node is the relative group-law identity on all parameter schemes and does not construct a dual or polarization.
lem-sfb-algebraically-trivial-line-multiplicativity vs thm-sc-theorem-of-cube: the cube identity for a field abelian variety and any line is different from multiplicativity of an algebraically trivial line on a relative group space over a possibly nonreduced parameter.
lem-sfb-abelian-h2-reduced-coproduct-injective vs lem-sfb-coherent-group-bialgebra: the latter is the Hopf/Kunneth description over a field and gives primitivity of H1, not absence of degree-two primitives; the new statement is injectivity in H2 over any affine parameter with arbitrary base-module coefficients.
lem-sfb-abelian-h2-reduced-coproduct-injective vs lem-sfb-abelian-structure-h1-dimension: a dimension equality for H1 over an algebraically closed field is neither the relative H2 assertion nor its arbitrary-coefficient form.

Whole-DAG statement/title/source searches, tag searches for 0DNM and lemma-picard-group-first-order-thickening, and blueprint_refs.py searches for Picard, abelian, coherent cohomology, theorem of the square, multiplicative, exterior, obstruction, algebraically trivial, coproduct and square-zero were made before creating these nodes. The plausible matches above were opened. No new node is elementary or a clause restating the lifting conclusion. The obstruction node is general deformation theory, multiplicativity makes no mention of thickenings, and the H2 assertion makes no mention of line bundles.

## Proof plans for the unsplit inputs

These are future-work notes, not proofs inserted into the new statements.

For the space obstruction, the proof of Stacks 0DNM gives the sequence of unit sheaves with additive kernel via a -> 1+a, on the equivalent small etale topoi. Hilbert 90 identifies Pic with H1 of units. The connecting map gives exactness. A square of thickenings induces a map of these exact sequences with the ideal coefficient map; naturality of connecting maps gives precisely the displayed equation. This general naturality is important: I did not assume pullback of the ideal equals the new ideal in an arbitrary square.

For multiplicativity, the target is triviality of the normalized difference line, not smoothness of the dual Picard space. One should use the relative theorem of the cube, the homomorphism defined by a line into the full rigidified Picard space, and rigidity for such homomorphisms to show that a fibrewise algebraically trivial line has zero difference. Identity normalization removes a line pulled back from the base. A proof based only on vanishing at geometric points of a possibly nonreduced scheme would be invalid; that gap is precisely why this is a new non-elementary input rather than an elementary step.

For the H2 input, the usual relative coherent-cohomology calculation has locally free cohomology commuting with arbitrary base change and the cup exterior algebra on H1. In degree two the (1,1) Kunneth component of the reduced coproduct is x wedge y -> x tensor y - y tensor x. Locally choose a basis e_i: coefficients of e_i tensor e_j with i < j recover each coefficient of e_i wedge e_j. Thus that component is split injective, so remains injective after tensor with any module N; one must not merely tensor an arbitrary injective map with N. A future split must establish these relative cohomology and comparison statements for spaces and all parameters, without using this item's lifting or the parent dual smoothness. They are not asserted to follow from the field Milne calculation alone. The current node states just the cohomological result needed, leaving its complete split to its own worker.

## Review by Q140

I read the item and its parent's public statement, Milne AV I section 8 printed pp.35--37 (especially Proposition 8.4(c) and Remark 8.5), the group-law construction before I Lemma 12.2 printed p.55, and Stacks spaces-more-morphisms.tex Tag 0DNM, label lemma-picard-group-first-order-thickening, including the proof. Milne's p.55 calculation uses etale cohomology with constant coefficients, not coherent structure coefficients, and therefore is used only as motivation for the explicitly agent-stated cohomological input. The relative source MFK is unavailable; the item has proof_origin.by = agent and the new nodes say exactly which extensions are not proved by the available field source. Every new statement introduces its base, group, parameter, ideal/module, cohomology convention and line module, with inline definitions where scheme-only definition nodes would not define space cohomology. The new nodes have no proof or proof dependencies.

Step 1 uses the actual statement of lem-sfb-stack-chartwise-smooth-etale-calculus for preservation of smoothness under arbitrary base change and for smooth implies flat; it does not take flatness from a definition. I read that node and checked the space chart convention. On a flat chart the tensor sequence has no Tor kernel, so the ideal is really O_B0 tensor I, not merely its image. Products use the same flatness. The relation I^2=0 descends the action through O_T0 and makes the resulting ideal square-zero. This is a short flat tensor computation, not a hidden general ideal-base-change claim.

Step 2 cites the new space obstruction's exact sentence giving a group homomorphism and its pullback equation, and the new multiplicativity statement giving m0* M0 = p1* M0 tensor p2* M0 for an arbitrary T0. The three maps are maps of the actual thickenings C0 subset C and B0 subset B. Their coefficient maps send f0*I to q0*I by the same base scalar action, so all three classes lie in H2(C0,K). This avoids a wrong comparison between ordinary module cohomology and units cohomology. The displayed equality writes out the entire primitivity calculation.

Step 3 cites the new H2 node with T0 affine and N = Gamma(T0,I), so its hypotheses allow arbitrary, non-finite and non-flat I. It gives injectivity of precisely m0* - p1* - p2*, not a different Kunneth or dual-Picard theorem. Exactness from the obstruction node gives an ordinary unrigidified lift and an isomorphism of restrictions. These two uses have verbatim quotes in citations.json.

Step 4 is elementary tensor normalization. I checked the variance of the dual: u:P0 -> O gives (u^{-1})^vee:P0^{-1} -> O. The formula p tensor lambda -> u(p) lambda(u^{-1}(1)) equals evaluation lambda(p), so the isomorphism reduces with exactly r0, not an arbitrary scalar multiple of it. No extension of a trivialization on T0 to T is assumed, and no theorem on lifting base line bundles is needed.

Step 5 observes directly that every map to a field kills I, so geometric fibres of the thickening agree and M has the same geometric fibres as M0. For the final base-change clause I read the statement of lem-sfb-space-flat-proper-fp-locality: it explicitly preserves properness and finite presentation under arbitrary space base change. Smooth base change is in the chartwise-calculus node; the group laws and the relevant geometric fibres are the pulled-back ones. Both uses are explicitly cited. I corrected this step during self-review to cite these preservation facts rather than hide them behind 'the hypotheses persist'.

Small cases checked: I=0 gives zero obstruction and an existing module; M0 trivial gives the trivial normalized lift; A of relative dimension zero (the identity group) has H2=0 and normalization returns O_T; empty T has the empty module and the identity cover. For the general obstruction, a split thickening has zero obstruction for an already pulled-back module, but no vanishing for all nonsplit thickenings is asserted. For multiplicativity, nonzero-degree ample lines are excluded, and no conclusion is drawn merely from set-theoretic vanishing on nilpotent parameters. For the H2 node, relative dimensions zero and one have zero source, N=0 has zero source, rank-two exterior classes map to e1 tensor e2 - e2 tensor e1, and in characteristic 2 the coefficient in the first coordinate is still 1, so the argument never divides by 2. The item asserts no uniqueness and the proof makes no such claim.

I reviewed B1--B10, C1--C8, D1--D5 and E1--E7 with the files open. No item statement was weakened, no restricted Noetherian T was substituted for arbitrary affine T, and no full dual-space theorem was invoked circularly. Every proof step is under 2000 characters. New searches were all made with msearch.py; actual outputs are retained. Loogle's ring Picard exactness result Submodule.mulExact_unitsToPic_mapAlgebra (Mathlib/RingTheory/PicardGroup.lean:859) was read and rejected because it is a faithful algebra's relative Picard sequence, not a sheaf H2 obstruction. The other semantic results are ring cotangent maps, unrelated group cohomology, or additive sheaf pullback; none is a one-line specialization of these relative geometric assertions. No unavailable search was represented as a negative search result.

## Unfinished work

No unfinished work within this one-level split. The three new prerequisites are intentionally statement-only stage-1 items. The missing MFK source is explicitly requested above; the delivered assembly is agent-written. Server delivery checks and the final push are recorded by deliver.py.
