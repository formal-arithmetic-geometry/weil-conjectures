# Stage-1 report: lem-sfb-etale-local-lift-torsor-quasi-coherent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-etale-local-lift-torsor-quasi-coherent.json: item, statement; direct scheme proof in seven steps using existing nodes. Mathlib verdict: no match for the entire scheme-sheaf assertion.
- citations.json: 21 step/node citations, with verbatim statements copied as the excerpts.
- report.md: this report. searches.jsonl is the unmodified log produced by msearch.py.

No new DAG nodes, no Mathlib leaves, no Lean files. This prerequisite is not the key node of its unit, so no unit realization fields change.

## Attachments

None. Searches for the item's blueprint tag and the lift/derivation/sheaf notion in lean/WeilConjectures found no project declaration stating every clause. Ring-level square-zero lift equivalences are not an attachment. Existing sorry-free module pullback quasi-coherence remains attached to its existing node.

## WANTED

None.

## Findings and corrections

The item statement, statement dependencies and inherited blueprint fields are retained. Its empty imported proof is now a direct scheme proof following the same Stacks square-zero derivation route. No smoothness, affineness of the test, or existence of lifts is added.

The first dry run exposed a genuine dependency cycle in my initial proposed use of lem-sfb-space-infinitesimal-lift-pseudotorsor. Although its statement generalizes this item, its proof dependencies run through space square-zero realization, thickening representability and space approximation, back to the flat-groupoid algebraicity bootstrap and the parent scheme smoothness criterion. I removed that citation and both space-comparison citations. The final proof constructs the scheme action directly using affine-target morphisms and explicit square-zero ring arithmetic. I checked dependency reachability for each final cited node; none has a path to this item. This repairs C6 without changing another worker's node.

The current blueprint read was literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). The inherited place explains the algebraicity/smoothness prerequisite through which this node serves that route. The unit/chapter routes are unchanged. blueprint_refs.py ancestor prints None for this inherited non-blueprint chain; the existing null ancestor, detailed place and via list are retained. Searches of the whole imported blueprint for derivation, pseudo-torsor, square-zero lifts and quasi-coherent Hom found no blueprint node stating the item; same_as is empty.

## Not duplicates

No new nodes are proposed. The whole-DAG search by Tags 061A/061C/061D and 04FH/04FJ/04FK found the general space pseudo-torsor theorem and lem-per-etale-local-lift-torsor-quasi-coherent. The former cannot be used here because its dependency route cycles, and the latter is another unsplit item, not evidence of a proof. Searches for finite presentation of differentials, Hom quasi-coherence, flat Hom base change, affine pushforward base change, and derivations found the lower-level nodes now cited. None was recreated, and no new lemma restates a clause of the item.

## Mathlib searches

I read and retained the inherited search records. I also ran msearch.py with this item's own id: LeanFinder in two different phrasings, Loogle for "Derivation", LeanSearch for the pseudo-torsor of square-zero scheme lifts, and grep for Derivation|KaehlerDifferential|torsor in AlgebraicGeometry. The five exact new queries and command log records are appended to mathlib_searches. All services answered. The inherited Loogle query containing the unknown identifier Sheaf.H is explicitly described as invalid in its retained result, not used as evidence of absence.

I read Mathlib/RingTheory/Derivation/ToSquareZero.lean:45-124: derivationToSquareZeroEquivLift is the algebraic bijection after fixing the algebra structure/lift, not a theorem about the scheme sheaf or its quasi-coherent coefficient. FormallyUnramified.lean:40 and :48-55 concern an unramified diagonal or uniqueness. Differentials/Presheaf.lean:96-106 gives a universal derivation. The second phrasing additionally returned a finite-presentation-to-quasi-coherence construction and Smooth/Basic.lean:189, whose finite-presentation assertion assumes formal smoothness. None proves the entire item under its hypotheses. These are no-match verdicts for the item, not assertions that the algebraic ingredients are absent.

## Review by NY

I read the source of the item in spaces-more-morphisms.tex: Tags 061A (lemma-sheaf), 061C (lemma-action-sheaf), 061D (remark-special-case). I read the direct scheme proof in more-morphisms.tex: Tag 04FG (lemma-difference-derivation), equation-D and the subsequent lemma-action-by-derivations, Tags 04FH/04FJ/04FK, and the final quasi-coherence paragraph of 02H6. The arithmetic omitted there is explicitly written in steps 5 and 6. I also read morphisms.tex 01V3 and 01QY, algebra.tex 00RY, modules.tex 01CQ, descent.tex 023Q, and the flat Hom/affine base-change inputs. There are no new nodes requiring additional source reviews. No SGA source is used.

For step 1 I opened every cited statement: def-sbc-locally-finite-presentation supplies the finite algebra charts; def-sc-relative-differential-sheaf identifies the module on them; lem-sfb-ring-finite-presentation-differentials is exactly the needed finite-presentation theorem without Noetherianity; lem-weil-pbc-quasi-coherent-finite-type-affine supplies the affine criterion. lem-pc-tensor-pullback-finite-presentation applies to a_0 without flatness. def-sbc-first-order-thickening supplies the quasi-coherent square-zero ideal. Over Spec A it is the A/J-module J, and localization verifies its quasi-coherence on the reduction. The hypotheses of lem-weil-pbc-sheaf-hom-finite-presentation-quasi-coherent are consequently satisfied. Finally lem-weil-pbc-closed-immersion-pushforward-annihilated(1) applies to the actual closed immersion i and this quasi-coherent Hom module. No finite type assumption on the ideal is needed.

For step 2 the statements of lem-weil-pbc-fpqc-finer-than-etale and lem-weil-pbc-fpqc-representable-descent give precisely descent and equality testing for arbitrary scheme-valued maps on the covering. The same applies after base change to U_0. Thus both equations defining a lift descend. I do not cite an algebraic-space representability result here.

For step 3 I read the seven cited statements. def-weil-etale-morphism includes flatness. lem-weil-pbc-flat-tensor-exact identifies the pulled-back ideal with JB; flatness of B/JB over A/J is the same exactness test after restricting to A/J-modules. The finite presentation of E from step 1 is exactly the hypothesis in lem-weil-pbc-flat-base-change-hom-finitely-presented, while I can be arbitrary. The affine tilde/gamma equivalence and the explicit tilde pullback formula identify the algebraic Hom base-change map with the sheaf Hom map on charts. Localization is flat, so the same Hom theorem identifies these maps on smaller principal opens; the displayed c tensor h formula fixes their compatibility. The closed immersion is affine by its quotient description, so lem-weil-pbc-affine-pushforward-base-change(1) applies to K. def-sc-etale-qcoherent-module evaluates the resulting u^*H by global sections. This proves that H_et(U) is the entire Hom group on U_0, including the restriction maps, rather than assuming that arbitrary internal Hom commutes with arbitrary base change.

For step 4 I read def-pc-module-pullback, lem-pc-module-pullback-adjunction, and lem-sfb-relative-differentials-sheaf-universal-property. Their statements give, successively, the composition identification, Hom adjunction, and the relative derivation bijection. The universal property permits an arbitrary module g_*I_U, which need not be quasi-coherent. All constructions are restriction-compatible. The relative base is W throughout, so the derivations kill the exact sections needed for fa=bu.

For step 5 the only additional non-elementary input is lem-weil-pbc-morphism-into-affine-scheme, whose statement is a bijection for an arbitrary source P. I check multiplicativity by expanding the product and dropping D(x)D(y) in the square-zero ideal; units and the base map follow from the derivation identities. The affine-target bijection realizes the resulting ring maps as scheme maps. Their reductions fix their underlying continuous maps, and their ring-sheaf maps agree on overlaps, so ordinary scheme gluing yields the desired lift. This is the scheme construction itself, not an invocation of the cyclic algebraic-space realization theorem.

Steps 6 and 7 are elementary calculations from the maps already constructed. Subtracting two lifts lands in the square-zero ideal; the product expansion proves Leibniz with the reduced module action, and equality over W proves relativity. Addition/subtraction are inverse, proving the orbit bijection. Zero and successive sums prove the action laws. Pullback preserves these formulas, so restriction commutes with the action, including further etale arrows. On an empty lift set the action is the unique empty map and asserts no section. No uncited existence or vanishing theorem occurs in these steps.

I tested I=0 (an isomorphism thickening, a singleton lift set, zero action), f=id_W (zero differentials and unique prescribed lift), and V=A^1_W with a dual-number test (translation is addition in the square-zero ideal). I also tested an obstructed example: W=Spec k[t], V=Spec k with t sent to zero, T=Spec k[e]/(e^2) with t sent to e, and T_0=Spec k. There is no W-map T->V; our action on the empty lift set is still valid. Arbitrary non-Noetherian affine A and a non-finitely-generated square-zero ideal require no extra hypothesis: only E is finitely presented. No intersections of arbitrary affine opens are assumed affine.

The final proof-dependency union is exact and every cited statement has a verbatim entry in citations.json. All seven proof steps have fewer than 2000 characters (the longest is 1512), and I inspected them for hidden independent comparisons. The two substantive comparisons in step 3 are explicitly the existing flat Hom and affine base-change theorems, not new clauses. Generic off-unit inputs are declared in split_report.tool_uses. Against B-E, no new statement-only node, duplicate or relabelled clause is introduced; the statement's existing definition dependencies are retained; every non-elementary proof input is cited; and no strengthening of available hypotheses is used. The first dry-run failure and its mathematical correction are recorded above.

## Unfinished work

None in the stage-1 proof split. Dependencies remain attached to existing DAG nodes for subsequent stages. No Lean was written and no compiler, Lake or global build was run.
