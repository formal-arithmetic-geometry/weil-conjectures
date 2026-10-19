# Stage-1 report: lem-coef-directed-decomposition-right-anodyne

## Files written

- `dag/nodes/sec-six-functors/lem-coef-directed-decomposition-right-anodyne.json`: statement node, split, no new Mathlib leaf.
- `citations.json`: verbatim citations for every non-elementary dependency used by each proof step.

## Attachments

No exact sorry-free declaration was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; the target id and the notions “right anodyne”, “directed”, and “decomposition” produced no declaration matching the full item.

## WANTED

- Archived HTT text for Proposition 4.2.3.8 and Remark 4.2.3.9, including Notation 4.2.3.1 for the decomposition simplicial set `K_F`. The online PDF was read for the route, but it is not present under `literature/`.

## What was checked and changed

The imported statement was retained. I searched the whole DAG and the current blueprint for the target and for the directed-decomposition/right-anodyne construction. The existing `lem-coef-infinity-directed-cone-cover` node cites this item but does not state it, so it is a genuine dependency rather than a duplicate. The existing `lem-coef-infinity-directed-union-local-colimits` concerns coherent colimit assembly and does not assert this simplicial right-anodyne inclusion. The existing join lemma, boundary-cell filtration, right-anodyne definition, and filtered-nerve weak-contractibility lemma are the smaller results used below; no new node is a restatement of an item clause.

## Review by Q24

I read the target node, its chapter record, the `sk-prop-sf-biduality-general` unit record, and the ancestor blueprint reference in `prop-coef-integral-exceptional-adjoint`. I also read the complete statements of `def-cbc-enhanced-diagrams-cones`, `def-coef-infinity-right-anodyne`, `lem-cbc-filtered-nerve-weak-contractibility`, `lem-coef-infinity-monomorphism-boundary-cells`, and `lem-coef-contractible-join-right-anodyne` before citing them. The Lean source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` contains no declaration tagged with this item and no declaration whose statement gives the displayed construction and conclusion.

Step 1 checks that the mixed-simplex formulas are closed under every face and degeneracy: deleting the first upper index uses the increasing inclusions `K_a ⊆ K_b`, while losing the lower or upper block lands in the specified pure summand. Its only external input is the simplicial-set convention in `def-cbc-enhanced-diagrams-cones`.

Step 2 introduces `I_σ`, the indices containing a fixed nondegenerate simplex. Covering makes it nonempty, and directedness of `I` plus monotonicity of the family gives a common upper bound still containing `σ`; because this is a poset, parallel arrows are equal. These are exactly the hypotheses of `lem-cbc-filtered-nerve-weak-contractibility`, whose conclusion is quoted verbatim in `citations.json`.

Step 3 filters the mixed construction by nondegenerate simplices of `K`, with each boundary already attached. For `σ` of dimension `m`, the new cells are precisely `Δ^m ⋆ N(I_σ)` attached along `∂Δ^m ⋆ N(I_σ)`. I checked the pure lower, pure upper, mixed, face, and limit-stage cases against the boundary-cell statement; no quasicategory hypothesis is introduced.

Step 4 applies the existing contractible-join right-anodyne lemma to each attachment, using Step 2 for weak contractibility, and then uses the defining closure of right anodyne maps under pushouts and transfinite compositions. The `m=0` attachment uses `∂Δ^0 = ∅`, so the vertex case is included. The final composite has source `H(∅)=N(I)` and target `H(K)=K_F`.

I tested the route on the edge cases of a singleton index poset, a two-element directed poset, an empty simplicial set `K`, and a cover containing degenerate simplices only through their nondegenerate ancestors. No hypothesis was added, no cone or quasicategory structure was assumed, and no SGA source was used. I ran the required Mathlib searches (LeanFinder, Loogle, grep, and LeanSearch); they found only general nerve, horn-generator, or directed-set declarations and no match for this right-anodyne decomposition theorem. The server-side `check_dag` precheck passed.

## Not duplicates

- `lem-coef-directed-decomposition-right-anodyne` vs `lem-coef-infinity-directed-union-local-colimits`: the latter assembles coherent colimits from local cocones; it does not define `K_F` or prove that `N(I) → K_F` is right anodyne.
- `lem-coef-directed-decomposition-right-anodyne` vs `lem-coef-infinity-directed-cone-cover`: the latter uses this target to prove cofinality of cone vertices and therefore cannot itself replace the target’s right-anodyne construction.

## Second reading by Q24

- Statement: checked the displayed degreewise formula and all hypotheses against HTT Notation 4.2.3.1, Proposition 4.2.3.8, and Remark 4.2.3.9 (printed pp. 248–252); the increasing-subset specialization has the stated (I_\\sigma), and the degenerate-simplex condition is automatic because simplicial subsets are closed under faces. Verdict: faithful.
- Step 1: checked every face and degeneracy at the lower/upper block boundary against the operator convention in `def-cbc-enhanced-diagrams-cones`; pure summands and the first-upper-index inclusion are handled. Verdict: elementary and complete.
- Step 2: checked the definition of (I_\\sigma), nonemptiness from the cover, finite upper bounds from directedness and monotonicity, and the equal-parallel-arrow condition against `lem-cbc-filtered-nerve-weak-contractibility`. Verdict: complete under the stated hypotheses.
- Step 3: checked the nondegenerate-simplex filtration and the pushout (∂\\Delta^m\\star N(I_\\sigma)\\to\\Delta^m\\star N(I_\\sigma)) against HTT Proposition 4.2.3.8 and `lem-coef-infinity-monomorphism-boundary-cells`; the boundary and limit-stage cases are explicit. Verdict: complete after clarifying refinement of coproduct cells.
- Step 4: checked the join application, the (m=0) case, and closure under pushouts/transfinite compositions against `lem-coef-contractible-join-right-anodyne` and `def-coef-infinity-right-anodyne`. Verdict: complete after making the coproduct refinement explicit.
- New node `lem-coef-directed-decomposition-right-anodyne`: checked B1–B7, source, definitions, duplicate search, and all three Mathlib search kinds; no additional node is introduced. Verdict: accepted.

Changes made: tightened steps 3 and 4 to state explicitly how coproduct cell attachments are refined into a transfinite sequence, and replaced the step-1 citation quote with the exact operator-convention sentence. Edge checks covered empty (K), a singleton and a two-element directed poset, (m=0) and (m=1), and degenerate simplices; all behave as claimed.
