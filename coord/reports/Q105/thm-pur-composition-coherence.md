# Stage 1 report: thm-pur-composition-coherence

## Files written

- `dag/nodes/sec-smooth-purity/thm-pur-composition-coherence.json`: item split into four proof steps; no new nodes.
- `citations.json`: verbatim statement quotations for every cited node in every step.

## Attachments

No attachment. `WeilConjectures.PurityFiniteSetting.nonempty_iso_dualizingComplex_comp` in `EtaleCohomology/Purity/Smooth/Basic.lean:361` is sorry-free, but it states only existence of the dualizing-complex composition isomorphism with chosen twist identifications; it does not state the target's canonical purity-map equality (nor its hypotheses and displayed composite), so it is not an attachment.

## WANTED

None.

## What was checked and changed

The item statement was checked against `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.md`; it agrees clause by clause with the finite coefficient datum, smooth separated maps of dimensions `d,e`, the source reassociation, and the final `c_{g,f}^{-1}` composite. The imported proof was rewritten from the current proof file rather than relying on the older master snapshot. No statement, hypothesis, or coefficient category was changed.

No new node was needed. Existing statements provide the smooth tensor formula and its composition clause (`thm-pur-cohomological-smoothness`), diagonal section invariant identification (`lem-pur-diagonal-base-change`), the canonical diagonal/DNC orientation (`thm-pur-diagonal-dualizing-object`, `thm-pur-dnc-invariance`), vector-bundle purity with direct-sum compatibility (`cor-pur-vector-bundle-purity`), etale local normal forms (`sbc-thm-etale-local-normal-form`), exceptional inverse-image composition (`def-weil-exceptional-inverse-image`), and twist construction (`def-coefficient-twists-detailed`). I searched the whole DAG and blueprint for tangent-composition, diagonal-composition, and purity-coherence nodes before deciding this.

## Review by Q105

I read the current blueprint statement and proof, the unit/chapter records, and every cited node's full statement. Step 1 uses exactly the composition clause of `thm-pur-cohomological-smoothness` and the finite exceptional-inverse-image construction; specializing to the constant coefficient object gives the displayed dualizing-object comparison. Step 2 uses `lem-pur-diagonal-base-change` for `C(p_1,Delta) = omega_f`, `thm-pur-dnc-invariance` for the unique normalized DNC comparison and its etale/base-change compatibility, `cor-pur-vector-bundle-purity` for the normal-bundle Tate identification and direct sums, and `sbc-thm-etale-local-normal-form` for the coordinate calculation. In those coordinates the tangent sequence is the split coordinate sequence; I checked the rank-zero case (`d=e=0`) and the affine-space model, where all maps reduce to identities. Step 3 checks twist tensor-power reassociation and the even shift, using the twist definition and the canonical dualizing identifications. Step 4 is the formal mate calculation through the two tensor adjunctions; the composition clause fixes the order and `c_{g,f}^{-1}`.

Every non-elementary input in these steps is cited by its node, and every `citations.json` quote is a verbatim substring of that node's statement. The two Mathlib search phrasings were run with LeanFinder, Loogle, grep, and LeanSearch; they found only ordinary smoothness/pullback composition results and no exceptional-inverse-image purity declaration. Lean source inspection found only the dualizing-complex existence theorem noted above, so no attachment was claimed.

## Second reading by Q105

I reread the current main-20261015 blueprint statement and proof (the node and Proof Steps 1--2) and checked the imported item statement clause by clause: the finite coefficient datum, smooth separated maps and relative dimensions, the displayed pullback/twist/shift reassociation, the order of the two purity maps, and the final inverse composition comparison all agree. I also checked the prior return: the sandbox statement has no added bounded-constructible hypothesis on the free (K), so it does not repeat the returned target-level alteration.

Step 1 was checked against the composition clause of `thm-pur-cohomological-smoothness` and the exceptional-inverse-image definition; the tensor formula specializes at the unit and its composition mate gives the displayed dualizing-object comparison. Verdict: PASS.

Step 2 was checked against the full statements of `lem-pur-diagonal-base-change`, `thm-pur-dnc-invariance`, `cor-pur-vector-bundle-purity`, and `sbc-thm-etale-local-normal-form`; these supply the section invariant, normalized DNC comparison, direct-sum compatibility, and local split tangent sequence used in the argument. `thm-pur-diagonal-dualizing-object` supplies the diagonal endpoint. The zero-dimensional case and affine-space coordinate model reduce to identity comparisons. Verdict: PASS.

Step 3 was checked against the twist definition, the diagonal-dualizing-object identification, and the tensor formula. Reassociation of tensor powers and even shifts gives exactly the displayed source identification; this is a two-line consequence of the cited interfaces, so `elementary: true` is appropriate. Verdict: PASS.

Step 4 was checked against the tensor formula's composition clause, the exceptional adjunction/composition interface, and the twist definition. Taking mates gives first `Lf^*(gamma_g)(d)[2d]`, then `gamma_f`, then `c_{g,f}^{-1}` in the stated order. Verdict: PASS.

The item has no new nodes. I checked every proof dependency's complete statement and found no duplicate or special-case node to add; the existing DNC, vector-bundle, diagonal, smooth-tensor, exceptional-inverse-image, normal-form, and twist nodes are the strictly smaller interfaces required by the four steps. The Mathlib searches recorded in `searches.jsonl` were rerun with alternative LeanFinder, Loogle, grep, and LeanSearch phrasings; they found only ordinary smoothness or pullback coherence declarations, never this purity-map theorem. Verdict: PASS for B1--B7 and C1--C5.

No node, statement, hypothesis, citation, or source was changed in this second reading. The only repair required by the prior return was already present in this sandbox: retaining the imported target's free (K) rather than adding the rejected (D^b_{ctf}(Z,A)) restriction. I retained the current main-20261015 `source`, `proof_origin`, and `blueprint_update` metadata and left the first worker review intact.
