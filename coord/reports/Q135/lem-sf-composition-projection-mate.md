## Files written

- `dag/nodes/sec-six-functors/lem-sf-composition-projection-mate.json`: unchanged statement, four assembly steps, 2106 proof characters.
- `dag/nodes/sec-six-functors/lem-sf-triangle-projection-normal-form.json`: statement, unsplit, no Mathlib match; local mate substitution, outer whiskering and intrinsic system repetition.
- `dag/nodes/sec-six-functors/lem-sf-refinement-projection-counit.json`: statement, unsplit, no Mathlib match; the identity-side mate calculation for the directed refinement map.
- `dag/nodes/sec-six-functors/lem-sf-cartesian-closure-refinement.json`: statement, unsplit, no Mathlib match; closure/density removes the unused clopen component of a supplied triangle.
- `dag/nodes/sec-six-functors/lem-sf-three-cell-compositor.json`: statement, unsplit, no Mathlib match; typed three-cell expansion, disjoint whiskering and refinement pasting.
- `citations.json`: an exact statement quote for every step/node citation.

## Attachments

None. The project declaration `AlgebraicGeometry.ProEtale.CompactCompositionProjection.compositionProjectionMate` in `lean/Sheaf/SixFunctors/CompositionProjectionMate.lean:297` ends in `sorry`. Searches of the actual upstream `lean/WeilConjectures/` by the blueprint tag and by projection/composition/refinement terminology found no finished declaration of this item. Mathlib's generic mate and whisker lemmas are not finished project declarations of this geometric assertion.

## WANTED

None. All sources used are present locally.

## Return repaired

This is the human-requested work redistribution, not an unchanged re-push. At entry the sandbox had only dispatcher marker files, no item JSON, report or searches. I copied the current shared item read-only; its eleven steps and all maintainer metadata are preserved in `returned-node.json`. I also preserved the prior Q126 report in `prior-report-Q126.md`. The initial required `deliver.py --no-push` exited with the expected missing-report diagnostic. The current main statement, Lean record, reviewed metadata, source and other maintainer fields are retained exactly; only split-owned proof fields and the split report change.

The return has one substantive point, repeated in its compiler-attribution paragraph: distribute all 9519 characters of argument into at least three comparable independent statement-only tasks, and make this item a short assembly. Four new obligations now carry the independent arguments; their inherited argument loads are 2146, 917, 1102 and 1413 characters respectively. They have empty proof/proof_deps, status unsplit, actual logged semantic/pattern/grep searches, self-contained statements, and explicit blueprint places and ancestry. The existing ringed-topos composition theorem already carries another 742 characters of the old argument, so I reused it rather than creating a duplicate. Open tensor composition is the 544-character elementary restriction argument and remains explicit in the assembly. The setup and final substitutions/threefold application are the assembly itself. Every original argument is reproduced verbatim below, with its destination; none was replaced by an assertion that coherence is automatic.

The new normal-form node is strictly intermediate: its right side still has two proper projection maps and two open tensor maps. It does not state the item's projection identity or its associativity clause. The item must still contract these factors using the existing proper composition theorem and the explicitly checked open restriction argument. The refinement node is a separate identity for a single directed proper refinement, not a clause about a two-map composition. The closure node is geometry only. The staircase node has no projection assertion and no compactification-existence assertion.

## Sources and searches

I read `fix-prop-projection-formula.proof.md` in main-20261015 (the composition/refinement/coherence sentence), `prop-sf-pf-coherence.proof.md` there (the pentagon and naturality paragraphs), and the closure unit's `_section.md`. I read Stacks `more-etale.tex`, labels lemma-shriek-proper-and-open (0F7B), lemma-shriek-proper-and-open-compose (0F7C), lemma-shriek-proper-and-open-compose-horizontal (0F7D), lemma-shriek-composition (0F7J), and lemma-pseudo-functor (0F7K). Stacks gives the etale construction; the ambient pro-etale/system extension in these tasks is explicitly agent-written. No SGA route is used.

Whole-DAG statement/concept searches included projection/composition, refinement/projection, Cartesian triangle, clopen/closure, disjoint whiskering and 0F7K. Whole-blueprint searches via tools/blueprint_refs.py included `projection composition`, `compactification refinement`, `composite counit`, `projection refinement`, `Cartesian triangle`, `proper/open`, `projection coherence`, `schematic closure`, `pseudo-functor`, and `ringed projection`. The closure search found the generic closure/density nodes, not its application to an arbitrary supplied triangle. The proper/open search found bounded/etale comparison and purity nodes. The ancestor command gives fix-prop-projection-formula; each new via list is [lem-sf-composition-projection-mate]. The pre-existing item's from.place remains precise.

For every new node I ran msearch.py with LeanSearch, LeanFinder, Loogle and a Mathlib grep; the semantic searches give two phrasings. The exact successful queries, hits and verdicts appear in each node and in searches.jsonl. None of these services was down. The Loogle queries mentioning Compactification and NatIso reported unknown identifiers, which are recorded as such rather than claimed exhaustive absence. The other searches cover their concepts. In particular the closure searches found `AlgebraicGeometry.IsImmersion.isPullback_toImage_liftCoborder`; I opened Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean:246-260. It factors an immersion into its image and coborder, but does not identify the restriction of that closure inside the supplied V or the proper refining triangle. Thus it is not a one-line specialization of the new closure statement. The more general semantic query found coborderRange, subscheme and the open factorization, not the extra-clopen-component argument.

For the staircase search, `CategoryTheory.mateEquiv_vcomp`, `CategoryTheory.NatTrans.exchange`, `CategoryTheory.TwoSquare.hCompVCompHComp`, and ordinary sheaf pushforward associativity are useful ingredients, not the assertion about the specified geometric raw comparison, its two explicit expansions and directed-refinement equations. I opened the generic mate source; it has no geometric compactification normalization. For the normal form and refinement searches, the returned general adjunction naturality and condensed-sheaf counit lemmas do not state the specified maps. No new node is a Mathlib leaf. I separately found the existing DAG theorem lem-sfb-ringed-projection-tensor-composition and read its full statement: it does give the old proper projection composition identity for arbitrary ringed topoi and unbounded inputs, so it is cited, not duplicated.

## Review by Q135

I checked the return against both the new node statements and the old eleven steps, with the source passages open. The item keeps every coefficient and geometric hypothesis, including arbitrary unbounded inputs, semilinear quotient transitions and potentially nonseparated structure schemes. No new statement is an implicit reference to the setting of its parent: each introduces its own schemes, coefficient rings, categories, functors, maps and hypotheses. Every new node is statement-only. The proposed proof arguments are retained in this report, not inserted into their statement/proof/proof_deps fields.

Assembly step 1 reads the finite-type-over-Noetherian statement (it needs a Noetherian base, supplied by the field), and the Noetherian-open-subscheme statement (it gives quasi-compactness of every open). This applies to inverse images of affine opens in each Noetherian source, and to the composite bj. The ambient pasting statement supplies exactly the compositors, normalized Gamma and domains used. The projection definition gives PF=S(delta) pi; it asserts no projection isomorphism, and none is used. This is setup from cited statements and definitions, not a new geometric lemma hidden in an elementary step.

Assembly step 2 uses the actual second displayed composition identity of lem-sfb-ringed-projection-tensor-composition, with u=p,v=s. Its ordinary unbounded ringed-topos hypotheses include both the small pro-etale sites and the simultaneous ringed diagram sites. Its projection is the adjunct of counit tensor identity, exactly our pi. The ambient pasting node identifies c with the conjugate compositor, so the direction in the step is pi_sp(c tensor 1)=c S_s(pi_p) pi_s. For the open equation, lem-sf-open-tensor-normalization explicitly supplies invertible delta, full faithfulness and identity after restriction, also on diagram sites. The common source is in the image via the two delta isomorphisms; both maps restrict to the same identity. This is the elementary argument, including its essential-image check, rather than a new duplicate theorem. The off-unit ringed-topos result is declared in split_report.tool_uses; it is a generic tool and replaces no unit route.

Assembly step 3 uses exactly the displayed equation in the new triangle normal-form statement. I checked the source GFK tensor L, target H(K tensor P_jP_qP_iP_sL), and the middle factor T=P_sL. Naturality of c,e and the two equations already established in step 2 give the displayed PF_gf(alpha tensor 1). Both pullbacks f,g are retained. The new node includes joint naturality and the intrinsic system equation, so there is no unstated inference from evaluations and no application of a bounded constructible integral realization theorem to arbitrary systems. The old steps 4,5,7 below retain the precise mate substitution, whiskering and postcomposition needed by the worker of that node.

Assembly step 4 uses the new closure statement for its actual two closed/proper refining maps, not only the existence of a closure. Compatible-tower's statement supplies both a prescribed-composite refining tower and common refining towers; cofilteredness supplies common refinements and equalizers for the finite list. All original compactifications are supplied, so the tower lemma's existence premise is satisfied; its statement does not require the structure schemes to be separated. Iterating it gives the staircase required by the new three-cell lemma. That lemma explicitly equates L,R, identifies them with the two binary-comparison paths and asserts compatibility with directed staircase refinements. The new refinement-projection statement gives exactly C_u(K tensor P_fL) PF^c2 = PF^c1(C_u K tensor 1). Applying the already proved binary projection equality twice on either path is then elementary. No inverse of C_u or an arbitrary Gamma is used to cancel an equality. I checked the A,C whiskering order against the diagram of 0F7K: path C then A+B and path A then B+C. Its typed normal forms are recorded in the new staircase statement.

For the normal-form task I checked the finite/system proper-open projection-mate statement at A=V,B=barX,C=Y,D=barY, M=J_jK,N=P_sL. Its statement allows non-Cartesian squares, gives both input-unrestricted coefficient clauses, and is precisely the equality old step 4 takes. Old step 5's Gamma naturality is with respect to delta_j, then pi_s naturality moves Gamma to the rightmost factor. Old step 7 gives the identical actual system equation and specifies the outside whiskering; the common paragraph of the new statement keeps all quotient transitions. In particular the ringed-diagram operations are not completed integral operations.

For the refinement task the square has left proper edge id_X and right proper edge u. The local mate with r=id and the identity counit gives pi_id=id. The outer proper compositor has orientation S_p2 S_u -> S_p1. These checks give the direction C_u:F2 -> F1 in its statement and in the preserved argument. The theorem needs no inverted comparison and makes no isomorphism claim for a projection.

For the closure task the finite-type field hypothesis makes the schemes Noetherian, hence quasi-separated; the quasi-compact open bj is eligible for the exact closure/density statement. The ambient square gives V clopen in barX times_barY Y. After base change of the closure inclusion, the complementary clopen part of W_Y misses the dense open X, so it is empty. Since the factorization is through an OPEN subscheme V, this gives a scheme morphism, and the resulting W_Y -> V is the base change of the closed immersion W -> barX. The closed-immersion/proper and composition statements of the old proof therefore apply. It is not the invalid inference that an image containment gives a factorization through an arbitrary immersion. This is the nontrivial argument the new geometric statement asks another worker to formalize.

For the staircase task I matched each of its proper/open cells and all functor orders to the A,B,C grid of 0F7K. Unlike the generic proper/open calculus theorem, this task is about the supplied ambient natural transformations without assuming they are invertible. Old step 10's geometric common-tower construction remains the cited tower/cofiltered assembly; the typed expansion and the refinement-pasting conclusion are the new task. The formal whisker exchange is useful but does not itself state either typed expansion.

Small cases checked: an identity proper edge makes pi_id the identity; two identity opens make the delta equation identity; a Cartesian square makes the selected clopen component the whole pullback. With X empty the closure and intermediate closure are empty, and both projection sides are zero. With an unused clopen component V inside barX_Y, the closure removes precisely its complement and retains nilpotents determined by the schematic closure, not just a reduced topological closure. Identity refinements give the single projection. Zero complexes give zero maps. Setting a staircase cell to an identity reduces L=R to the corresponding two-cell pasting equation. With all maps identity all comparisons are identities. None of these checks uses Tor amplitude, boundedness, finite-evaluation faithfulness or separatedness over k.

I checked the long-step rule: the parent now has no step over 2000 characters and its full proof has 2106 characters, below the requested 3000. The four independent new tasks have no proof steps at all. The old proof is fully retained below, and the mapping says where each argument is now performed. There is no statement dispute or weakening. All verbatim citation witnesses are from statements, not proof text; proof_deps is exactly the uses union. I preserved maintainer-owned fields and have not edited the shared repository, launcher or Lean.

## Not duplicates

- lem-sf-triangle-projection-normal-form vs lem-sf-proper-open-projection-mate: the existing local square identity is the input; the new task adds both outer functors, delta_j naturality and the explicit expanded source-to-target normal form, not the final projection equation.
- lem-sf-triangle-projection-normal-form vs lem-sf-composition-projection-mate: the normal form still contains two proper and two open factors and has no associativity/refinement clause; the item must contract those factors and assemble the remaining tasks.
- lem-sf-refinement-projection-counit vs lem-cbc-complete-proetale-refinement-exchange-coherence: the existing statement is exchange/coherence on witnessed constant-ring towers; the new statement is tensor/projection compatibility for arbitrary varying-ring systems and finite pro-etale inputs.
- lem-sf-refinement-projection-counit vs def-sf-constructible-projection-mates: the latter defines constructible coherence and assumes none of it; it is not the arbitrary-input directed-refinement theorem.
- lem-sf-cartesian-closure-refinement vs sk-lem-nagata-sketch-closure: the latter supplies generic closure and density; the new result removes an extra clopen component relative to a supplied proper/open triangle and gives two actual proper refining maps.
- lem-sf-cartesian-closure-refinement vs lem-cbc-compactifiable-compatible-tower: the existing result constructs a new Cartesian tower from prescribed compactifications; it does not give this closed-immersion refinement of an already supplied non-Cartesian intermediate V.
- lem-sf-cartesian-closure-refinement vs sk-lem-nagata-density-normalization: the latter compares support functors after closure, not the relative intermediate restriction into V and Cartesian refining triangle.
- lem-sf-three-cell-compositor vs lem-sp-proper-open-staircase: that statement assumes a calculus whose interchange maps are isomorphisms, and a staircase; this task retains the actual possibly noninvertible ambient/system maps and states their typed expansions and directed refinement equation.
- lem-sf-three-cell-compositor vs lem-sp-compactification-refinement-coherence: the latter assumes a complete invertible calculus and geometric-existence predicates; the new task is on a fixed supplied geometric grid with raw maps and no such invertibility premise.
- lem-sf-three-cell-compositor vs lem-sf-composition-projection-mate: the parent has the projection/tensor identity and its final compatibility; the new task is only the nonprojection three-cell raw compositor equation.
- lem-sf-three-cell-compositor vs lem-sf-etale-chart-adjoint-comparison: the existing Natural Hom comparison on an ordinary étale factored chart concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs lem-sfb-exact-compactification-unit-identity: the existing Identity normalization of the exact compactification unit concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs lem-sf-etale-chart-left-compositor: the existing Specified compact-support source comparison for an equal factored chart concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs sk-lem-geo-affine-local: the existing theorem concerns classical-cohomology affine purity and etale exceptional localization, not a raw three-cell comparison on arbitrary ambient inputs.
- lem-sf-three-cell-compositor vs lem-per-finite-exceptional-internal-hom: the existing Internal Hom adjunction for finite etale direct image concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs thm-sf-comp-composition: the existing theorem is bounded-below etale-origin composition; it does not identify the arbitrary-input ambient/system transformations.
- lem-sf-three-cell-compositor vs lem-amb-etale-adjoint-locality: the existing Etale localization of the ambient adjoint concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs lem-pur-etale-horizontal-double-counit: the existing Double-counit identification in an etale-horizontal square concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs def-pur-etale-horizontal-support-comparisons: the existing node defines Canonical etale compact-support, horizontal composition and base-change comparisons; it does not assert the raw three-cell equation on both arbitrary unbounded coefficient domains.
- lem-sf-three-cell-compositor vs lem-amb-etale-compact-comparisons: the existing theorem is bounded-below on small etale sites and does not give intrinsic arbitrary system maps.
- lem-sf-three-cell-compositor vs lem-pur-finite-etale-dualizing-normalization: the existing Finite-coefficient etale exceptional normalization and its dualizing comparisons concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs lem-sp-site-coherence-descent: the existing conclusion is only on inputs with etale-origin witnesses and prescribed site transport; the new one is intrinsic on arbitrary ambient/system inputs.
- lem-sf-three-cell-compositor vs lem-pur-etale-horizontal-support-mate: the existing Etale horizontal compact-support exchange is the composition mate concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs lem-pur-etale-sum-right-adjoint-coherence: the existing Coherence of normalized etale sum right adjoints concerns etale adjoint/compact-support or dualizing normalizations; it does not assert this nonprojection raw three-cell equation in both the arbitrary pro-etale and semilinear-system categories.
- lem-sf-three-cell-compositor vs lem-sp-finite-compact-site-coherence: the existing pro-etale conclusion uses bounded-below etale-origin witnesses and no varying-ring system domain.
- lem-sf-three-cell-compositor vs lem-amb-unbounded-compact-support-comparisons: the existing theorem is about constant-coefficient small-etale compact supports, not arbitrary ambient pro-etale or semilinear-system maps.
- lem-sf-three-cell-compositor vs lem-sp-compactification-refinement-coherence: the existing formal theorem assumes an invertible calculus and geometric-existence predicates; this task has a fixed raw ambient grid and no invertibility premise.
- lem-sf-three-cell-compositor vs lem-amb-compact-support-staircase-expansion: the existing expansion is on constant finite small-etale modules and stops before L=R; this task includes both unbounded pro-etale and intrinsic semilinear domains and their L=R/refinement equation.
- lem-sf-three-cell-compositor vs lem-sp-proper-open-staircase: the existing staircase theorem assumes invertible calculus data and has no actual ambient/system realization or directed-refinement assertion.
- lem-sf-three-cell-compositor vs lem-amb-natural-transformation-whisker-exchange: the existing equation is only the middle disjoint whiskering law and not the two normalized geometric path expansions or their refinement compatibility.
- lem-sf-three-cell-compositor vs lem-amb-derived-compact-support-composition-coherence: the existing theorem is only the structural c,e loop and has no proper/open cell maps or refinement conclusion.
- lem-sf-three-cell-compositor vs def-sp-proper-open-calculus: the existing node defines invertible calculus data; the new statement proves an equation about the specified raw ambient maps without assuming such data.

## Complete retained argument and work allocation

### Returned step 1

Destination: Assembly step 1 (definitions and Noetherian checks); common setting of the normal-form and refinement nodes.

All schemes in the supplied triangle are finite type over $k$. A field is Noetherian since its only ideals are $0,k$, so the finite-type lemma makes these schemes Noetherian. Each inverse image of an affine open under $j,b,i$ is an open subscheme of the Noetherian source of that map, hence quasi-compact by the open-subscheme lemma. Thus these opens, and $bj$, are quasi-compact, as required below. Work first on the finite-coefficient unbounded pro-etale categories. Write $P_h=Lh^*$, $S_h=Rh_*$ and $J_e=e_!$, and write $\pi_h$ and $\delta_e$ for the proper counit projection and open tensor maps. Use the triangle already supplied in the statement; do not replace it by a Cartesian triangle. Put $F=S_qJ_j$, $G=S_sJ_i$, $H=S_{sp}J_{bj}$ and $\gamma=\Gamma_{(b,i,q,p)}$. If $C:S_sS_pJ_bJ_j\cong H$ is the composite of $c_{s,p}$ and $e_{b,j}$ of the ambient pasting lemma, the specified normalization is exactly $\alpha=C\circ S_s(\gamma J_j)$. This is the definition of the comparison in the question, rather than a transport from an etale-origin composition theorem. The projection definition reads $\operatorname{PF}_f=S_q(\delta_j)\pi_q$, $\operatorname{PF}_g=S_s(\delta_i)\pi_s$ and $\operatorname{PF}_{gf}=S_{sp}(\delta_{bj})\pi_{sp}$, with the indicated pullbacks in each $\delta$.

Original cited nodes: lem-sf-ambient-proper-open-pasting, def-exchange-projection, lem-sf-open-tensor-normalization, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian.

Original source: literature/stacks-project/more-etale.tex; Tag 0F7J (lemma-shriek-composition), displayed compactification calculation; agent use of the supplied normalized map on its actual pro-etale domain.

### Returned step 2

Destination: Existing lem-sfb-ringed-projection-tensor-composition, quoted in assembly step 2. Creating another node would duplicate its exact ringed-topos identity.

For composable maps $u,v$, identify $P_{vu}=P_uP_v$ and $S_{vu}=S_vS_u$ by the conjugate compositors of the ambient lemma. The composite adjunction has counit $\varepsilon_u\circ P_u\varepsilon_vS_u$. The transpose of $S_v(\pi_{u;M,P_vN})\pi_{v;S_uM,N}$ is therefore $(\varepsilon_{u,M}\otimes1)\circ(P_u\varepsilon_{v,S_uM}\otimes1)\circ\mu_{P_uP_v}$: substitute the counit-transpose formula twice and use naturality of $\mu_u$ and the adjunction triangle identity. This is precisely the transpose defining $\pi_{vu}$ for that composite counit. Injectivity of the adjunction bijection gives, restoring $c$, $$\pi_{vu}(c_{v,u,M}\otimes1)=c_{v,u,M\otimes P_uP_vN}\,S_v(\pi_u)\,\pi_v.$$ This is a calculation of maps; no projection is inverted.

Original cited nodes: lem-sf-ambient-proper-open-pasting, def-weil-pbc-composite-adjunction, def-exchange-projection.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (lemma-shriek-proper-and-open-compose), 0F7D (lemma-shriek-proper-and-open-compose-horizontal); agent formulation for ambient pro-etale and ringed diagram categories, not an assertion that these Stacks lemmas themselves have those domains.

### Returned step 3

Destination: Explicit elementary open restriction calculation in assembly step 2; no new node for a two-line argument.

For opens $j,b$ and $M,N$ on their source and target, respectively, $$\delta_{bj}(e_{b,j,M}\otimes1)=e_{b,j,M\otimes P_jP_bN}\,J_b(\delta_j)\,\delta_b.$$ Indeed, the tensor source is isomorphic, by $\delta_b$ and $J_b\delta_j$, to an object in the image of $J_bJ_j\cong J_{bj}$. Both arrows become the identity on $M\otimes P_jP_bN$ after $P_{bj}$, by the open-unit normalization. Full faithfulness of $J_{bj}$ proves their equality. This uses restriction to the open, where it is fully faithful, rather than evaluation of a coefficient system.

Original cited nodes: lem-sf-ambient-proper-open-pasting, lem-sf-open-tensor-normalization.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (lemma-shriek-proper-and-open-compose), 0F7D (lemma-shriek-proper-and-open-compose-horizontal); agent formulation for ambient pro-etale and ringed diagram categories, not an assertion that these Stacks lemmas themselves have those domains.

### Returned step 4

Destination: New lem-sf-triangle-projection-normal-form, local mate substitution.

Put $T=P_sL$, $U=P_iT=P_gL$, $M=J_jK$ and $K'=K\otimes P_jP_qU=K\otimes P_fP_gL$. Apply the finite-coefficient clause of the proper/open projection-mate lemma to the actual commutative square $pb=iq$, with inputs $M,T$. It gives $$\gamma_{M\otimes P_qU}\,J_i(\pi_{q;M,U})\,\delta_i=S_p(\delta_b)\,\pi_{p;J_bM,T}\,(\gamma_M\otimes1).$$ The proper maps are exactly $q,p$ and the open maps are $b,i$; a Cartesian square is not required. The pullback identification $P_qP_i=P_bP_p$ is the one for this square.

Original cited nodes: lem-sf-proper-open-projection-mate.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (lemma-shriek-proper-and-open-compose), 0F7D (lemma-shriek-proper-and-open-compose-horizontal); agent formulation for ambient pro-etale and ringed diagram categories, not an assertion that these Stacks lemmas themselves have those domains.

### Returned step 5

Destination: New lem-sf-triangle-projection-normal-form, outer naturality/whiskering calculation.

Expand $\alpha_{K'}G(\operatorname{PF}_f)\operatorname{PF}_g$ using step 1. Naturality of $\gamma$ with respect to $\delta_j:M\otimes P_qU\to J_jK'$ replaces $\gamma_{J_jK'}J_iS_q(\delta_j)$ by $S_pJ_b(\delta_j)\gamma_{M\otimes P_qU}$. Substitute the equality of step 4, and use naturality of $\pi_s$ with respect to $\gamma_M$. The resulting map is $$C_{K'}\,S_sS_p\bigl(J_b(\delta_j)\circ\delta_b\bigr)\,S_s(\pi_p)\,\pi_s\,(S_s\gamma_M\otimes1).$$ The source is $GF K\otimes L$ and the target is $HK'$. Every substitution is inside a functor or a composite, so it preserves equality of derived maps.

Original cited nodes: lem-sf-ambient-proper-open-pasting, def-exchange-projection, lem-sf-proper-open-projection-mate.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (lemma-shriek-proper-and-open-compose), 0F7D (lemma-shriek-proper-and-open-compose-horizontal); agent formulation for ambient pro-etale and ringed diagram categories, not an assertion that these Stacks lemmas themselves have those domains.

### Returned step 6

Destination: Assembly step 3, using the existing proper composition identity and the explicit open calculation.

Apply step 2 with $u=p,v=s$ to replace $S_s(\pi_p)\pi_s$ under $c_{s,p}$ by $\pi_{sp}$. Apply step 3 with opens $j,b$ and tensor factor $P_{sp}L$ to replace $J_b(\delta_j)\delta_b$ under $e_{b,j}$ by $\delta_{bj}$. Naturality of the two compositors then makes the expression in step 5 equal to $$S_{sp}(\delta_{bj})\pi_{sp}(C_K\otimes1)(S_s\gamma_M\otimes1)=\operatorname{PF}_{gf}(\alpha_K\otimes1).$$ This proves the displayed finite-coefficient identity. In particular the input of $\alpha$ on its left side is $K'=K\otimes Lf^*Lg^*L$, retaining both pullbacks.

Original cited nodes: lem-sf-ambient-proper-open-pasting, def-exchange-projection, lem-sf-open-tensor-normalization.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (lemma-shriek-proper-and-open-compose), 0F7D (lemma-shriek-proper-and-open-compose-horizontal); agent formulation for ambient pro-etale and ringed diagram categories, not an assertion that these Stacks lemmas themselves have those domains.

### Returned step 7

Destination: New lem-sf-triangle-projection-normal-form, intrinsic system version; assembly step 3 contracts its factors.

Now work intrinsically in $D(\mathscr S_T)$, with $P,S,J$, tensor, units and counits from the simultaneous system models. The ambient pasting lemma supplies conjugate compositors on these unbounded system categories, so the transpose calculation of step 2 and the fully faithful open restriction calculation of step 3 apply to system maps. Crucially use the SYSTEM clause of the proper/open projection-mate lemma with $M=J_jK$, $T=P_sL$. It gives in $D(\mathscr S_{\overline Y})$ exactly $$\gamma_{M\otimes P_qP_iT}J_i(\pi_q)\delta_i=S_p(\delta_b)\pi_p(\gamma_M\otimes1).$$ Whisker this system equality by $S_s$ and postcompose by $C_{K'}S_sS_pJ_b(\delta_j)$. Naturality of the system $\gamma$ and $\pi_s$ gives the expression displayed in step 5. The two system identities from steps 2 and 3 turn that expression into the right-hand side displayed in step 6. All factors, including quotient transitions, belong to the same ringed diagram models; no evaluated equality or total-limit argument is used.

Original cited nodes: lem-coef-semilinear-derived-sections, lem-sf-ambient-proper-open-pasting, lem-sf-open-tensor-normalization, lem-sf-proper-open-projection-mate, def-exchange-projection.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (lemma-shriek-proper-and-open-compose), 0F7D (lemma-shriek-proper-and-open-compose-horizontal); agent formulation for ambient pro-etale and ringed diagram categories, not an assertion that these Stacks lemmas themselves have those domains.

### Returned step 8

Destination: New lem-sf-refinement-projection-counit, independent identity-side mate argument.

For later comparison of compactifications, take a proper refinement $u:c_1\to c_2$, $c_a=(j_a,p_a)$, so $uj_1=j_2$ and $p_2u=p_1$. Let $C_u:S_{p_2}J_{j_2}\to S_{p_1}J_{j_1}$ be $S_{p_2}\Gamma_{(j_1,j_2,1,u)}$ followed by the direct-image compositor. Apply the proper/open mate identity with $r=1$, input $K$, and tensor factor $P_{p_2}L$. The defining transpose for $\pi_1$ is the identity. Thus it reads $$\Gamma_{K\otimes P_{j_2}P_{p_2}L}\delta_{j_2}=S_u(\delta_{j_1})\pi_u(\Gamma_K\otimes1).$$ Apply $S_{p_2}$ and precompose by $\pi_{p_2}$; step 2 with $u,p_2$ gives $$C_u(K\otimes P_fL)\operatorname{PF}^{c_2}=\operatorname{PF}^{c_1}(C_uK\otimes1).$$ This proves the required refinement compatibility for arbitrary inputs, in both coefficient settings, without the bounded constructible/finite-Tor refinement lemma. It is an equation in the direction of the specified refinement maps and uses no inverse of $C_u$.

Original cited nodes: def-weil-compactifications-refinements, lem-sf-proper-open-projection-mate, def-exchange-projection, lem-sf-ambient-proper-open-pasting.

Original source: literature/stacks-project/more-etale.tex; Tags 0F7B (lemma-shriek-proper-and-open), 0F7C (lemma-shriek-proper-and-open-compose), 0F7D (lemma-shriek-proper-and-open-compose-horizontal); agent formulation for ambient pro-etale and ringed diagram categories, not an assertion that these Stacks lemmas themselves have those domains.

### Returned step 9

Destination: New lem-sf-cartesian-closure-refinement, independent closure/density argument.

An arbitrary supplied triangle can first be refined to a Cartesian one. Its induced $V\to\overline X\times_{\overline Y}Y$ is clopen by the ambient lemma. Let $W\hookrightarrow\overline X$ be the schematic closure of $X$ supplied by the closure lemma; its hypotheses hold because $\overline X$ is finite type over the Noetherian field $k$, hence Noetherian and quasi-separated. The open $W_Y=W\times_{\overline Y}Y$ has dense open $X$ and its complementary clopen piece outside $V$ misses $X$, so that piece is empty. Thus $W_Y\to\overline X_Y$ factors through the open $V$ and is a closed immersion there (restriction of the closed immersion $W\hookrightarrow\overline X$). The maps $W\to\overline X$ and $W_Y\to V$ are proper, and $W\to\overline Y$ is proper by composition. The induced open $X\to W_Y$ and $W_Y\to W$, with proper $W_Y\to Y$, therefore form a Cartesian refining triangle. All arrows restrict to the identity on $X$ and satisfy the original triangle equations. These are geometric operations; the refinement projection identity is already proved in step 8 on both coefficient domains.

Original cited nodes: lem-sf-ambient-proper-open-pasting, sk-lem-nagata-sketch-closure, lem-weil-pbc-closed-immersion-proper, lem-weil-pbc-closed-immersion-base-change, lem-weil-pbc-proper-composition, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated.

Original source: literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/sk-lem-nagata-sketch-closure/_section.md; Schematic closure and density; agent clopen-complement argument reducing a supplied non-Cartesian triangle to a Cartesian refining triangle.

### Returned step 10

Destination: New lem-sf-three-cell-compositor for expansions, interchange and refinement equations; existing tower/cofiltered existence statements are cited in assembly step 4.

First use step 9 for every supplied non-Cartesian triangle. For three composable maps, arrange compatible compactifications in one refining tower: apply the compatible-tower construction successively to the two adjacent pairs, then its common-refinement clause to compare two choices. The cofiltered compactification lemma permits incorporating any previously supplied compactifications; repeat for the finite list of ambient and intermediate schemes. In the resulting grid let $A,B,C$ denote the three proper/open cells of Stacks Tag 0F7K (lemma-pseudo-functor). As in 0F7K, one composition path uses $\gamma_C$ followed by $\gamma_{A+B}$ and the other uses $\gamma_A$ followed by $\gamma_{B+C}$, with their functor whiskerings. Vertical and horizontal pasting from the ambient lemma replace the rectangle maps by their constituent $\Gamma_A,\Gamma_B,\Gamma_C$. The transformations for $A$ and $C$ act in disjoint functor positions, so their two whiskering orders agree by naturality. The unital associative $c,e$ finish the equality on the common tower. Pasting applied to the squares between refining towers gives the same equation with the directed refinement maps inserted, so the construction is compatible with either original parenthesization and its specified comparison maps. This argument concerns the actual unbounded pro-etale or system transformations, not the bounded-below etale-origin compositor.

Original cited nodes: lem-cbc-compactifiable-compatible-tower, lem-cbc-compactifiable-cofiltered, lem-sf-ambient-proper-open-pasting.

Original source: literature/stacks-project/more-etale.tex; Tag 0F7K (lemma-pseudo-functor), grid A,B,C and last paragraph, using the ambient pasting identities rather than a change of coefficient domain.

### Returned step 11

Destination: Assembly step 4, two applications of the established binary identity along the two equal paths.

Apply the identity of steps 6 and 7 first to $(g,f)$ and then to $(h,gf)$, or first to $(h,g)$ and then to $(hg,f)$. Both identify the threefold iterated projection map with $\operatorname{PF}_{hgf}$ after the corresponding composition path. Step 10 equates those paths on the common tower, and step 8 intertwines every projection map with each directed refinement comparison to that tower. Consequently these projection identities commute with the associative compositor and with the comparisons between the two compactifications of $hgf$. Tensor parenthesizations are identified by the canonical tensor associator. Every constituent is natural in $K,L$ (the adjunction units/counits, open tensor maps, $\Gamma$ and compositors), which proves the claimed naturality. No step restricted $K,L$ or asserted that a projection map is invertible.

Original cited nodes: lem-sf-ambient-proper-open-pasting, def-exchange-projection, lem-sf-proper-open-projection-mate.

Original source: literature/stacks-project/more-etale.tex; Tag 0F7K and the pentagon paragraph of prop-sf-pf-coherence in blueprint main-20261015; explicit application of the preceding directed identities.

## What could not be finished

The four new obligations are intentionally left unsplit for parallel workers, as the human requested. There is no unnamed gap in the assembly. No Lean proof or compiler work was authorized or performed. Server dry run and delivery results are appended below after their commands exit.
