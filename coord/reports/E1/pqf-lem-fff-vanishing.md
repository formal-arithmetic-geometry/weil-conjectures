1. Files written

- `dag/nodes/sec-abelian-varieties/pqf-lem-fff-vanishing.json`: item split; no new nodes.
- `citations.json`: seven verbatim citations for the five proof steps.

2. Attachments

None.

3. WANTED

None.

4. Problems found

The imported proof was one paragraph and cited the formal-functions theorem, finite-fibre cohomology, coherence of higher direct images, and completion/Nakayama without separating their uses. I expanded it into five steps. The pointwise formal-functions theorem already in the DAG (`lem-weil-pbc-formal-functions-stalk`) subsumes the imported completion comparison, and `lem-pc-coherent-hi` supplies finite generation of the stalk. The finite infinitesimal neighbourhoods have the finite fibre as their underlying space; this is recorded as an elementary thickening observation, after which `lem-sc-noetherian-cohomology-above-dimension` and `lem-sc-zariski-module-abelian-cohomology-agree` give positive-degree vanishing. The final descent uses the existing Mathlib leaf `lem-weil-pbc-local-completion-faithfully-flat` together with `lem-weil-pbc-completion-finite-module-tensor`.

## Review by E1

I read the item source `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/pqf-lem-fff-vanishing.md`, the imported node, and the source statements of every cited node. Step 1 uses the exact conclusion of `lem-weil-pbc-formal-functions-stalk`: the completed stalk is isomorphic to the inverse limit of cohomology on the infinitesimal neighbourhoods. Step 2 checks the hypotheses needed for the dimension-zero vanishing: proper means finite type, the locally Noetherian target makes the source and closed thickenings Noetherian, and nilpotent thickening preserves the finite fibre as the underlying space. Step 3 uses the exact vanishing clause of `lem-sc-noetherian-cohomology-above-dimension` and its module-to-abelian comparison node, so each positive-degree term in the limit is zero. Step 4 checks `lem-pc-coherent-hi` applies with the given proper, locally Noetherian, coherent hypotheses and therefore the stalk is finite; it also reuses the formal-functions statement to identify the completed stalk. Step 5 checks the local ring completion is faithfully flat and that completion of a finite module is tensoring with the completed ring, so zero completion implies the stalk itself is zero. I verified every citation quote verbatim against its node statement and recorded all Mathlib searches run for the item. No statement or source clause was weakened.

## Second reading by E1

- Item statement: checked against Stacks Tag 02OE (Lemma 30.20.8) and its proof via Tag 02OC; proper, locally Noetherian base, finite fibre, coherent sheaf, and vanishing for every p>0 agree.
- Step 1: checked against `lem-weil-pbc-formal-functions-stalk`; its completion-to-inverse-limit isomorphism has exactly the stated X_n and F_n.
- Step 2: checked proper implies finite type, finite type over a locally Noetherian base gives a locally Noetherian source, closed thickenings remain Noetherian, and Spec(O_{Y,y}/m_y^n) has only y, so X_n has the finite fibre as its underlying space; finite and one-point cases are consistent.
- Step 3: checked against `lem-sc-noetherian-cohomology-above-dimension` and `lem-sc-zariski-module-abelian-cohomology-agree`; F_n is the pullback of the coherent sheaf and is quasi-coherent, so dimension zero gives H^p=0 for p>0. Empty and one-point thickenings give the expected vanishing.
- Step 4: checked `lem-pc-coherent-hi` under the exact proper/locally-Noetherian/coherent hypotheses and rechecked the formal-functions completion identification; coherence gives finite generation of the stalk.
- Step 5: checked `lem-weil-pbc-local-completion-faithfully-flat` and `lem-weil-pbc-completion-finite-module-tensor`; faithful flatness detects the zero finite module. The cases M=0 and a field local ring behave correctly.
- New nodes: none; B1-B7 and duplicate-node checks are vacuous. Existing cross-unit nodes were read at their statements, not their proofs.
- Changes: added this second-reading section only; no mathematical statement or proof step required repair after the direct source and dependency checks.
