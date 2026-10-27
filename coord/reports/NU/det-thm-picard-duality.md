# det-thm-picard-duality — NU stage 1

## Files written

- dag/nodes/sec-picard-framework/det-thm-picard-duality.json: item, statement; split by reuse of the existing equivalent reviewed theorem. Mathlib: no match.
- citations.json: verbatim statements covering all three step/node citation pairs.
- searches.jsonl: actual msearch.py results, retained in the sandbox.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. No unit record is edited: the item is a detail node of sk-thm-picard-rr, not its key statement.

## Attachments

None. I searched the live lean/WeilConjectures source for the exact item tag and for Picard duality, serreDuality, residueTrace, and genus_eq_arithmeticGenus. The exact item tag has no hit. I read Curve/RiemannRoch.lean (serreDuality at 795, the zero-dimensional statements at 902 and 943) and Curve/ResidueTrace.lean (serreDuality_residueTrace at 383). The first gives natural isomorphisms in complementary degrees, the residue declaration covers integral dimension-one q=1, and the zero-dimensional declarations cover dimension zero. These individual declarations do not alone state every clause of the imported item, including its componentwise trace and all-degree pairing naturality. I therefore make no full attachment claim based on the older sketch node's broad closed audit. No compiler or Lean writing was used.

## WANTED

None: the proof is a direct application of an existing DAG statement, not a new residue or duality argument requiring another source.

## Statement corrected

STATEMENT-DISPUTED: the imported statement covers possibly disconnected smooth proper curves but only defines its dimension-one trace in the parenthetical integral case. For example X=P^1_k disjoint union P^1_k is smooth proper and pure dimension one, but has no single function field K; the displayed integral residue construction does not define t_X on this X. The empty scheme also needs a trace convention. The corrected statement follows the already reviewed sk-thm-picard-duality verbatim: take n in {0,1}, apply the integral construction on connected components, sum their traces, set the empty trace to zero, and understand negative cohomology as zero. This clarifies the original source's intent and adds no connectedness, perfection, or H^0(O)=k hypothesis. The genus reference now names sk-def-curve, whose statement actually defines that genus, rather than def-sc-curves, whose live statement defines curve terminology only.

The source read for the item is literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-rr/det-thm-picard-duality.md and its .proof.md, at the latest snapshot main-20261023-1620 (COMMITS.txt). I also read dag/units/sk-thm-picard-rr.json and dag/chapters/sec-picard-framework.json. The item's proof paragraph proposes projective-space duality and the residue sequence. The existing sk-thm-picard-duality realizes that exact route and has an independent 2026-10-21 review documenting the same componentwise correction.

The direct citers are sk-thm-picard-rr and lem-sfb-line-section-first-order-obstruction. The former uses n=q=1 and a line bundle; the latter uses the trace pairing and its naturality on a smooth proper connected curve. Both uses remain valid. No citer is edited.

## Existing result and searches

I ran tools/blueprint_refs.py search for 'duality', 'Serre duality', and 'trace pairing', and ancestor for the item, and searched all dag/nodes for the notions and exact item id. sk-thm-picard-duality is the existing equivalent theorem; thm-sc-serre-duality-curve gives an abstract curve duality isomorphism but does not by its statement specify the residue trace or pairing naturality. det-thm-picard-pn gives projective-space cohomology only. No duplicate node is created. blueprint.same_as records the equivalent sketch theorem.

The item's msearch.py searches include leanfinder twice with different phrasings, leansearch, loogle twice, and two source greps. All services answered. Semantic hits were finite-dimensional evaluation/perfect-pairing linear algebra and Kaehler-differential constructions; none identifies the indicated coherent cohomology spaces with the specified residue trace. Loogle's broad duality hits were Tannaka representation theory, and both source greps had no match. Exact query text and results are in the item and searches.jsonl. No absent search or unavailable service is claimed as evidence. No new-node searches are needed because there are no new nodes.

## Not duplicates

No new nodes. The item reuses sk-thm-picard-duality instead of creating a second theorem for its clauses. This is reuse of an existing statement, not moving the item into a new node. A dependency traversal of the existing sketch's statement/proof closure found no path to det-thm-picard-duality, so the reuse creates no cycle.

## Review by NU

I read the current item statement and proof source, its actual unit sk-thm-picard-rr and chapter, and the full live statement and proof of sk-thm-picard-duality. Its hypotheses are exactly the intended arbitrary-field, smooth proper pure-dimensional curve and finite locally free module hypotheses. In particular I checked that its statement includes dimension zero, the principal-parts cokernel, the local Tate residue and its separable-point formula, the global residue theorem, perfection for every degree, coefficient-morphism naturality, and the genus specialization. These are statements of the cited node, not facts extracted only from its proof. The sketch's reviewed projective-line duality and residue-sequence route is retained; the item's unit explicitly cites the sketch's unit, so this is within its route.

Step 1 takes precisely these conclusions from sk-thm-picard-duality. I compared the trace maps: both use Tr(A/k) in dimension zero, Tate's k-linear residue sum on the same principal-parts cokernel in the integral dimension-one case, and the new explicit component sum elsewhere. Thus there is no arbitrary-trace-versus-residue-trace identification being smuggled into the step. The sketch does not require a perfect field or constants equal to k. The quoted statement contains all of those conclusions, including naturality.

Step 2 takes the n=q=1, F=O_X specialization and the dimension equality from the same statement. The cancellation O_X^dual tensor omega = omega is multiplication on a rank-one free frame, so is elementary. I read sk-def-curve's statement and checked that it defines genus as dim H^0(Omega^1) for exactly the smooth proper connected curve used here. The finite-dimensional equality is explicitly part of the cited theorem's final clause; it is not inferred from an unrecorded finiteness theorem. Both citations have whole-statement verbatim quotes in citations.json.

For statement notions I read every statement dependency inherited from the existing sketch: finite locally free sheaves, relative differentials, the function field, module cohomology, scalar cohomology operations and comparisons, principal parts, and local Tate calculus. The function-field statement explicitly supplies its arbitrary integral-scheme convention. The curve/genus definition now uses the current arbitrary-field sk-def-curve convention, avoiding the older algebraically-closed-only wording of def-sc-curves. These are only statement inputs; I do not use their proofs as unrecorded lemmas.

Against delivery-errors B1-B10: no new statement-only nodes, no undefined new objects, TeX has single escaped backslashes in parsed text, no invented Stacks tag, no Mathlib leaf or line-number claim, real logged searches, explicit blueprint same_as, and no unjustified attachment. Against C1-C8: each non-elementary assertion is already in the cited theorem's statement; every uses id is in proof_deps, the citation quotes are verbatim, and the route is the unit's cited sketch. The generic genus definition is declared as a tool use. Against D1-D5: no new node restates a clause, and no omitted source argument is being rephrased as a proof; the complete stronger result is already present and reviewed, so it is cited directly. Against E1-E7: all field, smoothness, properness, dimension and freeness hypotheses match; the same canonical module and trace are used throughout, and the correction is reported explicitly above.

Small cases: the rank-zero bundle gives zero spaces; X=Spec k and a finite separable extension give the ordinary algebra trace pairing; a disjoint pair of projective lines uses the sum of component traces, not a nonexistent function field; X empty has the zero map between zero spaces; out-of-range degrees are zero as in the reused theorem. Over an imperfect field no ordinary residue followed by an inseparable field trace is substituted for Tate's residue. No characteristic restriction is introduced. Each proof step is below 2000 characters, and the assembly has no hidden new lemma.

## Unfinished work

None. Required server dry run and delivery follow this report; the final command output determines success.
