# Worker report: thm-sf-ctf-stability

## Files written

- dag/nodes/sec-six-functors/thm-sf-ctf-stability.json — existing statement, split; no Mathlib match. Fourteen proof steps replace the returned five-step split.
- citations.json — all 60 step/node pairs, with verbatim current statements of the 54 distinct dependencies.
- report.md — this repair and review.

New nodes: 0. New Mathlib leaves: 0. No dependency node was edited. The item's statement, statement dependencies, Lean record (absent), Lean audits, blueprint update, chapter and unit are unchanged. Its existing unit realization already assigns the statement and both unit paragraphs to this item and needs no edit.

## Attachments

None for the whole item. Read slopmaster2 WeilConjectures/SixFunctors/Etale/Derived/Stability.lean 124–150: it explicitly omits coefficient-passage clause (vii). The preservation declarations in Stability/{Basic,DirectImage,UpperShriek,OpenImmersion}.lean cover only individual clauses. The exact item tag/concept search in WeilConjectures finds no declaration supplying every clause. Upstream master sorry declarations are reference material only.

## WANTED

None. Read the current source at literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-kunneth-verdier/thm-sf-ctf-stability.proof.md, its statement file, and the older master item. The current blueprint_update proof has the same five-paragraph route. Read its unit and chapter records, GOAL.md, dag-sync.md, SETUP's three levels, the stage-1 brief and delivery-errors B–E in full.

## Returned defects and repair

The return requires retaining the statement and Lean record and replacing the non-elementary arguments hidden in old steps 1 (4676 characters) and 5 (2338 characters) by short steps citing their own nodes. The sandbox initially contained only its brief markers and searches.jsonl, not a node/report/citations; the returned five-step text was recovered from the current shared node. The prior Q31 report in coord/reports/Q31/thm-sf-ctf-stability.md was read and its hypotheses, route, corrections and search history retained. This is a substantive re-split, not an unchanged re-push.

Old step 1 is now steps 1–8. Its coefficient-dual evaluation argument is the existing general ringed-site lemma lem-sfb-ringed-site-perfect-duality (Stacks 08JJ). The finite constant-matrix refinement and perfect-model shortening are replaced by the existing stronger generic lem-sf-site-perfect-tor-window (Stacks 08G7, 08H5), whose conclusion gives a local finite-free-retract model in the precise input Tor interval. The dual-complex degree and bounded-flat tensor calculations remain short explicit steps citing their model, restriction, K-flat and Hom-computation statements. General Hom preservation and the affine-line example remain in their original places.

The origin example had an additional C4/E1 defect: lem-pur-gysin-structure assumes e(E/Q_ell) divides n, but the item permits every n>=1. Step 8 now cites cor-pur-affine-space-zero-section-purity with c=1 and B=Spec k; that existing node explicitly states Ri^!A=A(-1)[-2] for every n>=1. This follows the same Kummer/zero-section purity route and introduces no SGA source. Step 7 keeps the exact etale stalk calculation and explicitly identifies its pro-etale realization by the canonical direct-image mate. During citation review I replaced an essential-image citation, which did not itself assert full faithfulness, with lem-exc-proetale-closed-fully-faithful, whose statement explicitly gives the counit and full faithfulness used to detect nonzero pushforward.

Old steps 2, 3 and 4 are now steps 9, 10 and 11, unchanged verbatim, including sources and uses. Old step 5 is now steps 12–14. The residue, integral Hom/duality, coherent exceptional tower and common-stage retract arguments are applications of the existing statements lem-coef-integral-residue-tor, cor-coef-integral-internal-hom, lem-coef-integral-hom-reduction, thm-coef-integral-verdier, prop-coef-integral-exceptional-adjoint, thm-coef-rational-verdier, lem-coef-rational-operations and thm-coef-qbar-verdier. In particular the coherent normalized tower is specified in the integral exceptional-adjoint statement, and retract compatibility and the formula (E,K) -> (E,D_E K) are in the qbar theorem's statement. Neither argument is reconstructed or assumed inline.

No statement dispute is introduced in this repair. The historical STATEMENT-DISPUTED repairs already in the returned statement (the distinction between tensor and Hom intervals and nonnegative dimension bounds for empty schemes) are retained unchanged. There is no unrestricted unbounded pro-etale adjunction or arbitrary levelwise-tower effectivity claim.

## Searches and duplicate decisions

Read and retained searches.jsonl and the item's full mathlib_searches history. The retained semantic search concerns constructible finite-Tor six operations and returns generic derived-category t-structure bounds; the Loogle CategoryTheory.Tor search returns generic Tor declarations; the retained LeanSearch failure is a rate limit and is unavailable, not evidence of absence. No new search is invented or added to mathlib_searches. No node is created, so no new-node Mathlib search or leaf claim is needed.

Whole-DAG searches by tags 08JJ, 08JH, 08JB, 08DQ, 08DM and by finite-projective/Tor-window/constant-matrix/dual-tensor notions found the existing generic duality and Tor-window nodes. Read their full statements and sources. Whole-blueprint searches used blueprint_refs.py ancestor thm-sf-ctf-stability and search with site-perfect, coefficient dual, strictly perfect, residue, origin, normalized tower, coherent realization and the exact item title. The exact title finds only this item. The origin search found the all-finite-level zero-section purity node. No elementary fact, existing specialization or clause of the item was made into a new node.

## Not duplicates

No new nodes. Reuse lem-sfb-ringed-site-perfect-duality and lem-sf-site-perfect-tor-window rather than creating duplicate coefficient-duality/model-shortening lemmas. prop-sf-dualizable-hom and lem-sf-hom-finite-projective additionally assume a six-functor datum, which the item's local coefficient-site argument does not assume. The generic ringed-site lemma is the appropriate existing statement. The integral-adjoint and qbar nodes already state all the specific tower/retract information used in the former long paragraph.

## Review by N7

I read the current five-paragraph blueprint proof and the older returned proof together, and opened every dependency statement used by each resulting step. For the generic local tools I read Stacks sites-cohomology.tex 08JJ (lemma-dual-perfect-complex), including the local bounded model and evaluation calculation, and 08G7 (lemma-perfect-precise), including the final model in degrees a through b; 08H5 supplies restriction of Tor amplitude. For the integral exceptional operation I read the current full DAG statement and main-20261015 sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md. The current statement's explicit coherent realization is stronger precision than the blueprint's shorthand, so the item applies that statement directly.

Step 1: lem-sf-pullback-tor-amplitude says bounded constructibility and unchanged [a,b]; lem-sf-tensor-ctf(ii) says bounded constructibility and [a+c,b+d]. def-weil-finite-tor-amplitude defines the subcategory they enter. All separated finite-type and coefficient hypotheses are the item's.

Step 2: lem-sfb-ringed-site-perfect-duality explicitly states the canonical evaluation isomorphism for any ringed site and arbitrary second derived object. def-weil-site-perfect-complex supplies precisely the bounded local finite-free-retract hypothesis at finite coefficients. No six-functor datum is smuggled in.

Step 3: lem-sf-site-perfect-tor-window explicitly states existence of a model in [a,b] on each localized cover, not just local perfectness in unspecified degrees. Its general ringed-site statement applies on either small site and includes arbitrary module-sheaf tests, avoiding the previous constant-test descent argument.

Step 4: lem-pc-bounded-exact-term-hom-quasi-iso applies because Hom from a finite-free retract is exact, by the written retract calculation. def-pur-derived-internal-hom defines the K-injective model to which this comparison maps. lem-weil-pbc-ringed-internal-hom-exact-restriction explicitly gives the slice restriction comparison. def-pur-hom-complex gives degree r dual term (P^{-r})^vee; dualizing the splitting proves it remains a finite-free retract. This degree reversal is an elementary calculation after the cited model results, not an asserted global model.

Step 5: lem-pc-bounded-above-flat-kflat-site supplies K-flatness; lem-sf-flat-model gives L in [c,d] on both coefficient sites. The exact slice restriction statement and monoidal pullback statement justify restrictions of that model and its flatness. lem-weil-pbc-site-derived-tensor-descent gives the actual total tensor model. Degree sums give [c-b,d-a]. K-flatness computes tensor with an arbitrary test sheaf, and local vanishing of sheaf cohomology gives the global bound. No uniform cover over all integral reductions is used.

Step 6: cor-weil-finite-constructible-hom states preservation and precisely [c-b-2m,d-a+2m] on either site; X is separated finite type and m>=0.

Step 7: the finite-stalk formula applies to the finite origin immersion. The exact and conservative etale stalk statements and the stalk tensor statement say precisely what is used to prove flatness; no pro-etale geometric-stalk conservativity is assumed. The canonical-mate comparison applies because the closed origin immersion is qcqs and the constant input is bounded below. Tor comparison (i) carries the etale intervals to the pro-etale realization; closed pro-etale exactness applies because the complementary G_m is quasi-compact.

Step 8: stratum-ambient-Hom says RHom(Rs_!P,M)=Rs_*RHom(P,Rs^!M) on the pro-etale site for the Noetherian affine line. With P=A it becomes Ri_*Ri^!A. The existing zero-section purity statement supplies Ri^!A=A(-1)[-2] for all n>=1, and exact closed image converts Ri_* to i_*. The fully-faithful closed image statement has no extra constructibility hypothesis and detects the nonzero rank-one twist. This corrects the ramification-divisibility mismatch without changing the example or the item.

Step 9 (old 2): all-sheaf vanishing gives UDV(f,A;2d), since A is finite ell-primary and ell is invertible. The direct-image theorem and pro-etale corollary provide the stated Tor bound. Nagata applies to the qcqs target. The proper middle scheme is finite type and separated over k, open extension preserves the interval, and constructible origin supplies exactly the domain of compactification coherence.

Step 10 (old 3): the open-complement theorem gives both vanishing and constructible direct images needed by prop-exc-closed-tor; Noetherianity gives the quasi-compact complement. Smooth admissibility gives the signed -2r shift. The chart theorem and its datum corollary supply assembly with the recorded c_U. thm-sf-preservation-class concerns the constructible exceptional functor. lem-coef-finite-exceptional states its dual formula and cor-coef-finite-verdier with the identity quotient gives the two dual intervals. Their composition is [a-2d_X,b+2d_Y]. thm-fix-general-biduality supplies the anti-equivalence, not merely preservation.

Step 11 (old 4): lem-fix-operation-reduction supplies pullback, tensor and compact-support comparisons. lem-coef-finite-direct-image supplies the counit-defined direct-image map. Constructible origin gives a bounded etale representative and Tor-amplitude reflection (ii) supplies its finite-Tor hypothesis. thm-coef-finite-hom supplies general evaluation-defined Hom comparison. cor-coef-finite-verdier and lem-coef-finite-exceptional supply the exact evaluation/biduality and unit/counit comparisons and cocycles. Each quotient has 1<=m<=n.

Step 12: lem-coef-integral-residue-tor explicitly concludes category equality and supplies one interval for all canonical reductions. Integral internal Hom and Hom reduction explicitly give membership and evaluation-defined reductions. thm-coef-integral-verdier gives the anti-equivalence and actual bidual map. These statements concern completed coefficient sheaves and a single derived-complete input, as does the item.

Step 13: prop-coef-integral-exceptional-adjoint explicitly supplies the coherent realization before total limit, completed-pullback dual formula, preservation, reductions, Tor bound and actual adjunction maps. R=O_E and the given separated finite-type f satisfy every hypothesis. Residue Tor supplies its uniform input interval. No independently chosen lift or arbitrary tower effectivity is asserted.

Step 14: thm-coef-rational-verdier states rationalization and field-extension cocycle; lem-coef-rational-operations identifies the specified operations and preserves evaluations and adjunction maps; thm-coef-qbar-verdier states the representative formula, exceptional adjunction and compatibility with retracts. Thus the common-stage/retract argument is already a cited statement, rather than hidden inside this step.

Small cases: zero complexes; empty X or Y with nonnegative dimension bounds and zero output; a point with m=0; a=b and c=d for the dual-degree reversal; n=1 and a ramified E with e(E/Q_ell)>1 (the reason to use all-finite-level purity); K=L=A[-1] on a point, where Hom has degree zero; and the origin in A^1, where supported Hom has degree two. These distinguish tensor from Hom intervals and verify the signs and the site's coefficient category. All new arguments use existing nodes, and no new unsplit statement requires a separate small-case test.

All 14 non-elementary steps are below 2000 characters (maximum 1748 in unchanged old step 3). There is no long-step loophole or elementary flag hiding content. The item's proof dependencies are exactly the union of uses; citations quote actual statements. Off-unit generic tools are declared in split_report.tool_uses with their purposes. No new node, Lean edit, compiler, Lake/build, agent, direct git command or shared-project/launcher edit was used. The required delivery tool prepares and checks a fresh delivery on the current server base.

## Unfinished work

None within this one-level stage-1 split. The cited unsplit nodes remain their own future stage-1 items. Dry-run and delivery evidence follow.
