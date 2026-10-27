# Stage-1 delivery: lem-fd-fixed-pair-mixed-square-lift

## Worker report

Files written:
- `dag/nodes/sec-fourier-transform/lem-fd-fixed-pair-mixed-square-lift.json`: the item, now split into five elementary calculations. Statement and statement dependencies unchanged. Fresh Mathlib searches appended to the inherited searches.
- `citations.json`: literal statement quotations for every step/node citation.
- `report.md`: this report and the self-review.
- `searches.jsonl`: actual msearch.py results, retained by the search command.

## New nodes

None. There are zero new Mathlib leaves; the two already existing definition dependencies are Mathlib leaves. No statement-only task or clause of this item has been created under another name.

Attachments: none. The project defines `CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso`, `mapOfNatIsoHom`, `mapOfNatIsoIsoOfIso`, `compCommIso`, `mapOfNatIsoCompIso`, and `mapOfNatIsoCompIsoOfIso`. These give portions of the construction, but no declaration located states all the four-category mixed-square, exact formula, inverse, arbitrary matched coherence, and inclusion clauses of this item. I therefore make no exact attachment claim.

WANTED: none.

What was incomplete: the live item was a statement-only auxiliary task, with no proof. I supplied the arrow check, the oriented cancellation of the mixed square, the naturality calculation at theta, the inverse/naturality check, and the componentwise coherence argument. The statement is well typed and was not corrected or weakened. No work remains in this stage-1 split.

## Sources and blueprint

I read `GOAL.md`, the chapter and unit records for sec-fourier-transform/sk-def-trace, the current main-20261015 source `blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`, the current DAG statement of def-fd-trace-function, and the inherited argument recorded by Q35 in `coord/reports/Q35/lem-fd-frobenius-fixed-pair-comparison.md`, especially old steps 8–10 (retained below). The physical blueprint file contains the trace prescription, not the literal abstract mixed-square theorem. The inherited source.place's reference to a final compatibility sentence belongs to the expanded coefficient-pair interpretation in the DAG/returned argument. I keep the maintainer-owned source field unchanged, and mark this proof as agent-written; it is not attributed to an unstated theorem of the paper.

The ancestry command returned def-fd-trace-function, through lem-fd-frobenius-fixed-pair-comparison and lem-fd-rational-coefficient-category-comparison, as already recorded. The exact inherited from.place is retained. Steps 2–4 spell out old steps 8–9; step 5 spells out old step 10. Step 1 checks the pair transports these calculations use. This does not change the chapter or unit route.

I read the full statements of the only two cited nodes, def-nagata-category (category composition and its laws; original source Stacks Tag 0014) and def-weil-endofunctor-fixed-pair-category (objects, intertwining condition, composition and faithful forgetting). The proof uses no additional Stacks theorem. There is no SGA citation.

For comparison, I read the project sources:
- `WeilConjectures/Mathlib/CategoryTheory/Endofunctor/Algebra.lean`, lines 260–330: transports and lifted natural transformations;
- `WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/IsoAlgebraComp.lean`, its Map section: lifted isomorphisms and composite transport;
- `WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebraCompIso.lean`, lines 24–59: compatible composite comparison.
These confirm the orientation/construction, but are not used as uncertified theorem citations.

## Searches and nonduplication

I searched the entire project WeilConjectures source for the blueprint id, fixed-pair notions and mixed-square phrases, and inspected its endofunctor algebra files. Whole-DAG searches used fixed-pair/fixed pair/endofunctor algebra/Endofunctor.Algebra and mixed-square/four-category phrases. Blueprint searches used `fixed pair`, `fixed-pair`, `endofunctor`, `mixed square`, `commuting functors`, and `transport`. No blueprint statement of the abstract mixed square was found; same_as remains [].

The nearby lem-fd-fixed-pair-equivalence-transport requires J to be an equivalence and proves an equivalence rather than the mixed square. The statement of lem-pur-natural-comparison-functor-transport changes the endofunctor on each side of one functor using kappas; it does not compare the two composites around this four-category square. These statements were opened, not used as proxies. Other mixed-square hits are application/coefficient data, not a more general proof of this item. No new node is being distinguished or added.

All fresh Mathlib queries were executed using msearch.py with group NU and this item id. LeanSearch, Loogle, LeanFinder and grep all answered. A second semantic phrasing was tried. Results and exact query strings are appended to the node from searches.jsonl, preserving the inherited searches. I read Mathlib/CategoryTheory/Endofunctor/Algebra.lean at lines 145–205 and CategoryTheory/Action/Basic.lean at lines 470–500. Algebra.isoMk supplies individual algebra isomorphisms; functorOfNatTrans and its composition isomorphism change endofunctors on one fixed category; mapActionCongr treats monoid actions. None states this item or is a one-line specialization to its full assertion. Hence this item is split, not a Mathlib leaf.

## Review by NU

I checked B–E with the statement and cited definitions open. There are no new nodes needing independent sources or statement-only checks (B1–B8). The item's statement introduces all four categories, their endofunctors, functors and comparison isomorphisms, including a common sufficiently large universe. Its existing notion dependencies cover categories and fixed pairs. I retained its single-backslash TeX and blueprint metadata (B9). I checked the project declarations above for an exact attachment, rather than treating a related transport construction as the entire result (B10).

Step 1 cites def-weil-endofunctor-fixed-pair-category for the object and arrow condition and underlying composition. It constructs the inverse of the transported structure and writes the complete arrow calculation using naturality of c and the assumed intertwiner. Identities and composition follow directly from L's functor laws. This is a few-line calculation, not an appeal to a theorem about transport hidden behind a definition citation (C1–C4).

Step 2 cites def-nagata-category for associative composition and identity cancellation. The inverse equations used here belong to the supplied natural isomorphisms. Left multiplication by Tp(b0 inverse) followed by rp inverse and right multiplication by J1(rs inverse) followed by b1 inverse are given explicitly, so the use of inverses has the correct order. Both resulting arrows go from G1 J1 Ts K to Tp J0 F0 K. No equivalence, inverse functor or invertibility of an arbitrary morphism is assumed.

Step 3 cites the fixed-pair definition for exactly its intertwining condition. I expanded both composite structure maps and wrote naturality of j at theta, whose source is F0 K, not K. Substituting the equality from step 2 gives the claimed exact formula. This uses the assumed mixed square, not a coherence theorem about scheme pullbacks. There is no intermediate lemma needed beyond associative substitution.

Step 4 again cites the fixed-pair definition, including faithfulness of forgetting. Multiplication by j inverse and G1(j inverse) proves the inverse-component intertwining equation. I explicitly wrote the naturality equation for a pair arrow and explained cancellation giving inverse naturality. The inverse laws are underlying inverse laws and then equality of pair arrows. Thus invertibility of the lifted component is proved rather than presumed from a definition (C4/E5).

Step 5 uses precisely the cited definition's faithful forgetful functor. I specified how identity, composition, inverse and each whiskering acts on components; consequently each assumed underlying coherence equation yields the same component equation of pair arrows. The equal-source/equal-target-pair-functor hypothesis is retained: faithfulness does not identify objects or two different pair structures. Inclusional transports use their own stipulated commutation isomorphisms and the identical formula. No fullness, faithfulness, equivalence, scalar-ring or geometric hypothesis on the four transporting functors appears anywhere. This checks both the generality and the limitation of the coherence clause (E1, E4, E6).

For C5–C8/D1–D5, all nontrivial-looking assertions have their short argument in the steps; none is moved into a new node or taken from a cited node's proof. The only proof citations are two existing definitions/Mathlib leaves, so there is no cycle or off-unit theorem route. Each step is under 1000 characters. I checked the long-step instruction: there is no step over 2000 characters and no concealed comparison lemma or identification left unproved.

Small cases (E2/E3): with all functors and comparisons identities, the formula reduces to theta = theta. Empty source categories make the assertions vacuous and do not require choosing objects. The functor to a terminal category verifies the construction does not need faithfulness or equivalence. With F and G identity functors, pair objects are objects with automorphisms, as the formulas require. To check the noncommutative order, I also ran a direct Python matrix calculation in the one-object category with morphism group GL_2(F_5). I used four inner-conjugation endofunctors and inner-conjugation transporting functors; the comparison component from conjugation by A to conjugation by B is B A^{-1}. The supplied mixed square holds. For every one of its 480 invertible structure matrices theta, both the displayed intertwining identity and the inverse-component identity hold. This is an edge-case check, not a replacement for the written proof.

No mathematical statement error was found. The correction made during self-review was terminological: the cancellation step now says multiply on the left/right, avoiding an ambiguous precomposition/postcomposition description. All citations have verbatim statement excerpts in citations.json. The original statement, statement dependencies and no-equivalence/general-inclusion scope are unchanged.

## Retained inherited argument

The following is the original application argument from Q35, old steps 8–10; the abstract proof above supplies the elementary details it calls rearrangement/cancellation.

### Old step 8

For a finite extension $E\subset L$, denote the two scalar functors by $T_s,T_p$, their supplied Frobenius comparisons by $r_s:T_sF_{s,E}\simeq F_{s,L}T_s$ and $r_p:T_pF_{p,E}\simeq F_{p,L}T_p$, and the coefficient comparison by $j:J_LT_s\simeq T_pJ_E$. These are the actual scalar functors and comparisons in $S$. Its mixed square, with $b$ oriented as in the statement, reads
$$r_{p,J_EK}\,T_p(b_{E,K})\,j_{F_{s,E}K}=F_{p,L}(j_K)\,b_{L,T_sK}\,J_L(r_{s,K}).$$
This is an assumption of the given compatible transformation, not an additional coherence assertion about scheme composition.

Uses: def-fd-pullback-comparison-datum, def-fd-coefficient-comparison-datum

### Old step 9

The structure on the scalar extension of $(K,\theta)$ is $T_s(\theta)r_{s,K}^{-1}$. Naturality of $j$ at $\theta$, followed by rearrangement of the equation in step 8, gives
$$\begin{aligned}
j_KJ_L(T_s(\theta)r_{s,K}^{-1})b_{L,T_sK}^{-1}
&=T_p(J_E\theta)j_{F_{s,E}K}J_L(r_{s,K}^{-1})b_{L,T_sK}^{-1}\\
&=T_p(J_E\theta b_{E,K}^{-1})r_{p,J_EK}^{-1}F_{p,L}(j_K).
\end{aligned}$$
This is exactly the intertwining condition for $j_K$ between the two scalar-extended transported pairs. On arrows its naturality is that of $j$. Hence $j$ lifts to the required natural isomorphism of pair functors; its inverse also intertwines by cancelling this equation.

Uses: def-fd-pullback-comparison-datum, def-fd-coefficient-comparison-datum, def-weil-weil-sheaf-complex

### Old step 10

The same displayed calculation applies to a finite-stage inclusion $I_s:\mathcal C_{s,E}\to\mathcal C_s$ and $I_p:\mathcal C_{p,E}\to\mathcal C_p$: replace $T_s,T_p,J_L$ by $I_s,I_p,J_X$. Here $r_s,r_p$ are their specified pullback comparisons. The datum says the common-stage coefficient functor preserves the field label and that the component of its pullback comparison at a literal pair is the inclusion of the finite component. Thus the equation in step 8 for these substitutions is the specified finite-to-common comparison equation. Step 9 proves that the coefficient inclusion comparison is an isomorphism of Weil pairs, natural in arrows. This proves commutation with every finite-stage inclusion. The scalar cocycle and identity equations remain true after lifting: their underlying maps are the supplied ones, and arrows of pairs are equal exactly when their underlying arrows are equal.

Uses: def-fd-pullback-comparison-datum, def-fd-coefficient-comparison-datum, def-weil-weil-sheaf-complex

