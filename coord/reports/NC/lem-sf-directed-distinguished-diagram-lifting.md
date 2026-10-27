## Files written

- `dag/nodes/sec-smooth-purity/lem-sf-directed-distinguished-diagram-lifting.json`: nine-step replacement of the returned proof; statement and statement dependencies unchanged. No new nodes or Mathlib leaves.
- `citations.json`: verbatim statement excerpts covering every cited node in every proof step.
- `searches.jsonl`: the five original NC searches remain intact. No searches were repeated or attributed to this repair.

## Attachments

None. The original source searches found no finished project declaration stating the item; the attached Verdier existence theorem is sorried and uses this item.

## WANTED

None.

## Returned delivery and live comparison

I read the retained proof returned at 2b8322d4688 and the latest review supplied in the dispatch. The live item is still unsplit, and its statement is identical to the retained statement. The repair changes the proof, proof dependencies, proof origin, split status and split report; it retains the live source, statement dependencies, blueprint reference and search history. The delivery tool constructs the branch against the current server state; no repository git command was used.

## Repair of every returned point

The previous assertion that eventual equalities suffice for a family rebuilt with fresh sigma was incorrect. The review's nilpotent-twist example explains why equality in P does not imply that such moving final-stage formulas eventually agree. The new proof never uses that family. Steps 1--4 first assemble all primitive arrows, exact witness triangles, and witness isomorphism components at ONE base stage b. Step 5 evaluates entire expressions in C_b and proves recovery there using beta naturality and beta shift-add/shift-zero coherence. Step 6 applies the quotient criterion to fixed maps of C_b, obtaining H(p_b)=H(q_b) for one transition H=T_{bN}.

Step 7 then transports by exactly the construction requested in the return: A_v=a_{i_vbN,x_v}, kappa_{v,n}=A_v[n] sigma_{bN,n,B_v}, and Q(e)=kappa_w H(e) kappa_v^{-1}. Its two displayed identities prove preservation of shifts from CommShift of H; composition, addition, zero and negatives follow from functoriality, additivity and cancellation. Neither sigma_{i_vN} nor associator CommShift occurs in this calculation. Step 8 separately derives final recovery through the theta cocycle, theta-beta-sigma equation for (b,N), beta naturality and theta naturality. This replaces the old ill-typed equation that regarded a shifted e_N as a map on T_{i_vN}(x_v[n]). Step 9 uses this same Q on the triangle and inverse equations, including the shifted first-component equation, and uses exactness and TR1 closure to prove distinguishedness.

## Review by NC

I reread all three cited statements: def-sf-directed-common-stage-data, def-weil-pbc-triangles-with-shift and def-weil-triangulated-category, as well as the current filtered pair-model proof, Basic.lean's representative/equality/isoToStage calculations, the hypotheses of Shift.lean, and StageSystemVerdier.lean. Shift.lean assumes associator CommShift, whereas our datum does not; the repair uses only the individual CommShift structure of the single transition H.

Step 1 uses exactly D_S's existential distinguished witness and the triangle definition's componentwise inverse and square equations. Step 2 uses representatives, finite directed upper bounds, beta and sigma with their correct right-to-left orders. Step 3 uses the specified theta representatives and cocycle, then the exact theta-beta-sigma identity to prove base recovery. Step 4 uses exactness from the datum and its meaning in the triangulated definition, and explicitly checks the connecting map sigma T(h) against beta j_i(h); witness arrows are kept equal to these exact stage maps rather than replaced by unrelated lifts. Step 5 writes the beta naturality identity and the endpoint identity with both source and target shift-add comparisons. Composition cancels the common d, and additive constructors use the stated additivity. Step 6 derives the unnormalized diagonal criterion from the quotient and naturality of a_{bbN}, so it never assumes T_{bb}=1. Step 7 derives its shift identity from sigma for H and naturality of shift-add with A; these are the supplied natural comparisons and their shift-add coherence. Step 8 writes the delta cocycle, the (b,N) theta-beta-sigma identity, and the endpoint equality that combines them; theta naturality then proves recovery of Q(e). Step 9 checks a triangle isomorphism in C_N and applies the cited TR1 clause there, without presupposing a pretriangulation on P.

I checked the review's example with independently twisted sigma_{0N}: it does not affect the argument, since all fixed-base equalities are killed by a single H and all final constructor maps use sigma_{bN} only. I also checked empty families (take b above m_0 and N=b if there are no equations), repeated labels, arbitrary positive and negative shifts, nonidentity T_{bb}, and the shifted equation phi_1[1]h=q phi_3. Auxiliary witness labels are fresh but original shared labels remain shared. All nine steps are below 2000 characters; each displayed comparison is proved inline from the cited datum, and no separate non-elementary black box is hidden. Citation quotes were checked against the live statements, proof_deps equals the union of uses, no new node or off-unit tool lemma is introduced, and no SGA source is used.
