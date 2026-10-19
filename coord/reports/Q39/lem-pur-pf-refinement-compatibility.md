# Stage-1 report: lem-pur-pf-refinement-compatibility

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-pf-refinement-compatibility.json`: repaired four-step proof; no new nodes; Mathlib searches retained with no match.
- `citations.json`: verbatim citations for every node used by every repaired step.

## Attachments

None. The reference Lean source and upstream master source contain no sorry-free project declaration tagged or named for this item.

## WANTED:

None.

## What was wrong or corrected

The returned review identified four faults. I repaired the hidden mate identification by citing `def-sf-refinement-comparison-isomorphism` and `lem-sf-proper-open-comparison-site-normalization`, and I explicitly specialized `lem-sf-proper-open-projection-mate` to the refinement square. I expanded the proper composition calculation through (p_1=p_2v): the displayed formula for π through (c_{p_2,v}) is obtained from the pasted counits of `fix-prop-adjunctions` (3), the composition-compatible pullback/tensor maps of `lem-pur-derived-pullback-tensor-iso`, and `lem-weil-derived-direct-image-composition`; naturality of the counit-defined π in its first argument then moves β_v through the (p_2)-projection. I removed the unused `lem-pur-finite-projection-action-laws` citation. The only statement used as a generic tool outside the `sk-prop-an` route is `lem-sf-proper-open-projection-mate`; it is declared in `split_report.tool_uses` with its reason. No new node was added, so the batch-5 closure is unchanged.

## Not duplicates

`lem-pur-pf-refinement-compatibility` vs `lem-fix-projection-compactification-comparison`: the existing node assumes constructible finite-Tor inputs and packages the comparison across coefficient stages; this item treats the finite witnessed bounded-below domain and proves the explicit counit-defined PF square.

`lem-pur-pf-refinement-compatibility` vs `lem-pur-finite-projection-action-laws`: that node proves tensor-action identities for one fixed compactification; this item proves compatibility of projection maps with a proper refinement comparison. The action-law node is no longer cited.

## Review by Q39

I reread the item statement against the source sentence “Independence of the compactification: compatibility of the refinement comparisons with the counits and with (j_!), together with naturality” in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/prop-sf-pf-coherence.proof.md`, lines 15–17. The hypotheses remain exactly the separated finite-type (k)-schemes, proper refinement equations (vj_1=j_2) and (p_2v=p_1), finite coefficient datum, and three bounded-below etale-origin witnesses; no constructibility or finite-Tor hypothesis was added.

Step 1 reads the full statements of `def-sf-refinement-comparison-isomorphism`, `lem-sf-proper-open-comparison-site-normalization`, and `lem-sf-proper-open-projection-mate`. The first gives θ_v as (P_2(β_v)c_{p_2,v}), the second fixes the named pro-etale proper/open map by the transported etale comparison, and the third says that the normalized proper/open map is the adjunction mate Γ_v. Thus Γ_v=β_v^{-1} is now supported by statements that actually identify the maps. I also checked `def-weil-pbc-etale-origin-witness` for the retained witness data, `prop-compactification-coherence-detailed` for the witnessed domain, `def-exchange-projection` for the counit-defined PF maps, and `lem-weil-derived-direct-image-composition` for the compositor.

Step 2 reads the complete proper/open mate identity and substitutes (A=C=X), (B=\overline X_1), (D=\overline X_2), (k=j_1), (i=j_2), (r=\mathrm{id}), (p=v), and (N=Lp_2^*L). It records the specialized equation, observes directly from the counit definition that π_id is the identity, and uses the refinement equations and the canonical pullback comparison from `lem-pur-derived-pullback-tensor-iso`. The cited normalization and refinement-comparison statements say exactly why every Γ_v in this equation is β_v^{-1}.

Step 3 reads `fix-prop-adjunctions` (3), whose pasted unit/counit formula supplies the composite counit, `lem-pur-derived-pullback-tensor-iso`, whose statement supplies compatibility of the pullback/tensor comparison with composition, and `lem-weil-derived-direct-image-composition`, whose statement supplies the canonical (c_{p_2,v}). I wrote the resulting equation for (c\,\pi_{p_2v}) explicitly and used the naturality clause in the statement of `def-exchange-projection` to move β_v through π_p2. Applying that equation to (J_1K,L) and applying (Rp_{2*}) to Step 2 yields the two displayed PF composites, with the endpoint identifications checked from (p_1=p_2v), (vj_1=j_2), and (Lj_2^*Lp_2^*L\cong Lf^*L). No projection map is inverted.

Step 4 uses only the identity, transitivity, common-refinement, and cocycle clauses of `prop-compactification-coherence-detailed`, plus the identity and associativity clauses of `lem-weil-derived-direct-image-composition`; these statements justify cancellation of intermediate comparisons and independence of the common refinement. I checked the identity-refinement case and a common refinement with either leg an identity. The only inverses used are the normalized comparison isomorphisms θ_v and β_v. The off-route mate lemma was checked as a generic ambient tool under the batch-5 closure rule; it does not replace any `sk-prop-an` purity step. All new and retained Mathlib searches remain recorded in `searches.jsonl`; none matched.

## What could not be finished

Nothing remains for stage 1. The required dry run is the remaining delivery check.
