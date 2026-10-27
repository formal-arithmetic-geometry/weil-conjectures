# Review of N9 sk-thm-groth-ss, head 83112f5072d8 (stage 1, maintainer reader)

Verdict: FIX.

## What this delivery is
The branch has one commit on base 24f49cd. It touches only the item, the unit's realized fields and the report, and adds no new nodes. This is another re-push in the "side completion promotion" loop that follows earlier heads 14ee54f1cae7, cf9f63e2901b, 271ec0e4e99f, 6491366b6736, bcbb86209085, 57b7d5747844, c1fca0f8f400, and so on. Each of those was reviewed in full and fixed by re-inserting reviewer step 9.

## Delta against the returned head 14ee54f1cae7 (checked by script)
- Item: only `proof` and `split_report` differ. Of the proof, only step 7 differs. Its `uses` are unchanged, and it adds one sentence: "The zero object is injective: every restriction map into it is a map between singleton Hom sets and is surjective."
  The sentence is correct. Hom(N,0)→Hom(M,0) is a map between one-point sets, so it is surjective and 0 is injective. All terms of J→J→0→… are therefore injective, and the length-zero resolution legitimately computes R^{>0}h_*(J)=0.
- Unit `dag/units/sk-thm-groth-ss.json`: byte-identical to the 14ee54 head.
- All 29 statement/proof dependencies and the realization carriers: byte-identical between the two snapshots, and all exist in this snapshot. There is no changed dependency statement to re-check.

## Full reading of the mathematics (10-step fixed proof)
- Steps 1–2: Cartan–Eilenberg resolution of C=Φ(I•) (lem-sp-cartan-eilenberg-exists) and the signed finite totalization (def-sp-double-complex-total). On the first page, 'E_1^{s,t}=R^tΨ(C^s), which is 0 for t>0 by sk-def-groth-ss acyclicity. The augmentation square identifies d_1 with Ψ(d_C), so 'E_2^{s,0}=R^s(ΨΦ)(A) (Stacks 015J/015N, homology 0130/0132).
- Steps 3–4: the first spectral sequence collapses to one row. The bidegrees (s+r,1−r) and (s−r,r−1) are handled explicitly, and the stable page is n+2. Inverting the filtration inclusions with zero cokernels gives u_n: H^n(Tot D)≅R^n(ΨΦ)(A) with an explicit inverse v_n. At n=0 the composites are empty. Correct.
- Step 5: second filtration via lem-sp-cartan-eilenberg-properties with the indices exchanged. The (−1)^{pq} rescaling is an involutive chain isomorphism, and at characteristic two all signs are 1. This gives ''E_2^{p,q}=R^pΨ(R^qΦ A). Correct.
- Step 6: the filtration is transported along u_n with the same Q_p and e_{p,q}. E_∞=E_{p+q+2} matches the convention of sk-def-groth-ss, and the pages r≥2 are retained (def-sp-spectral-sequence). Correct.
- Step 7 (head delta included): small sites have enough injectives. f_* is additive and left exact because kernels and finite products are sectionwise. f^{-1} is exact, so f_* preserves injectives (lem-sp-right-adjoint-preserves-injectives; Stacks sites-cohomology 0734). The direction of the Hom restriction is right, and injectives are h_*-acyclic. Correct.
- Step 8: (hf)_*=h_*f_* holds on objects and morphisms (lem-weil-pbc-site-morphism-composition), with one common complex K. The punctual target is read as sections of the whole topos (Stacks 0732). Correct.
- Step 9 (reviewer step, dropped again by this push): for étale sites, base change gives morphisms of sites (lem-weil-pbc-sets-etale-inverse-image-exact). The isomorphism (W×_ZY)×_YX≅W×_ZX gives (hf)_*≅h_*f_*. For Zariski sites, lem-sc-topological-pushforward-injective applies. Γ(Y,−) is evaluation at the final object Y. Without this step, step 8 only calls the scheme sites "instances", which leaves C1/E5 open.
- Step 10: the module case uses lem-weil-pbc-module-pushforward-injective-acyclic at V=Y (Stacks cohomology 01EX), with forget-scalars acyclicity on one common resolution. Γ(Y,f_*M)=Γ(X,M). Properness and coherence only specialize the result (01F2/01F6). Correct.
- No SGA source is used. The item is not in a dropped list, and no re-split note applies. The statement is unchanged against base: no target is weakened and no hypotheses are altered.

## Fault and fix
Fault C1/E5, the same as on every earlier head: the scheme→site step (reviewer step 9) is missing again.

Fix written to `fixes/dag/nodes/sec-picard-framework/sk-thm-groth-ss.json`:
- Base: the 14ee54 fix. Script check: its steps 1–8 and 10 equal the 14ee54 head's steps 1–9.
- `proof[6]` is replaced by this head's step 7.
- `proof_deps` is the union of the step uses (25 ids).
- `split_report` is the fix's, with this head's summary plus one reviewer sentence. The 10-step blueprint mapping and the 12 tool_uses (accepted, unchanged) are kept.
- Script checks: only proof, proof_deps and split_report differ from the head. Every [id] in a step is in that step's uses and exists. The longest step is 1963 characters.

Maintainer: the split is mathematically approved. Please land or promote this fix (L) instead of re-dispatching the item, because every re-push drops step 9.
