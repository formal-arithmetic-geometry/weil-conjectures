Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-open-curve-boundary-higher-direct-image-vanishing.json` (statement, split; no Mathlib match).
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-gm-strict-henselization-stalk-formula.json` (statement-only helper; no Mathlib match).
- `dag/nodes/sec-curve-estimates/lem-sc-strict-henselian-dvr-fraction-brauer-zero.json` (statement-only helper; no Mathlib match).

Attachments: none.

WANTED: `literature/stacks-project/etale-cohomology.tex`, discussion preceding Tag 03RM, for the strict-henselization stalk calculation and boundary Brauer vanishing.

The item was unsplit and has no project declaration tagged with its blueprint id. The existing `prop-weil-pbc-strict-henselization-stalk-formula` is restricted to torsion sheaves, so it cannot be cited for `G_m`; the new helper records the non-torsion formula used by the source. The existing `cor-sc-hilbert-90-field` exactly supplies degree-one vanishing. The fraction-field Brauer assertion was absent from the DAG, so it is recorded as a separate statement-only helper. The interior-point argument is elementary from the definition of an open immersion and is kept as a proof step rather than a node.

## Review by J1

I read the target node, its neighboring comparison node `lem-sc-open-curve-gm-direct-image-cohomology`, and the ancestor `lem-sc-brauer-zero` route. I checked the source references in the imported node against the Stacks discussion preceding Tag 03RM. Step 1 uses the new stalk-formula statement exactly for the map from a higher direct-image stalk to cohomology over the strict henselization. Step 2 uses only the local isomorphism property of an open immersion, so it is marked elementary. Step 3 uses the existing Hilbert 90 statement for q=1 and the new strict-henselian-DVR Brauer statement for q=2; the hypotheses identify the boundary local ring as a strict henselian DVR and its fraction field as the field in both cited statements. I searched the DAG, blueprint references, Lean source, and Mathlib for each helper and recorded no match; LeanSearch was unavailable in both helper searches. I also verified the small cases q=1 and q=2 separately and supplied verbatim citations in `citations.json`.

What could not be finished: the source PDF/text is not present in this checkout, so the cited Stacks discussion is marked WANTED and the two helpers remain unsplit statement-only nodes.

## Not duplicates

lem-sc-strict-henselian-dvr-fraction-brauer-zero vs lem-sc-open-curve-boundary-higher-direct-image-vanishing: the helper states only Brauer vanishing for an arbitrary strict henselian DVR fraction field, while the item asserts vanishing of two higher-direct-image stalks for a specific open curve.
lem-sc-strict-henselian-dvr-fraction-brauer-zero vs lem-sc-brauer-zero: the helper concerns a field arising from a strict henselian DVR, while lem-sc-brauer-zero concerns the Brauer group of a smooth separated connected curve over an algebraically closed field.
lem-sc-strict-henselian-dvr-fraction-brauer-zero vs lem-sc-open-curve-etale-leray-low-degree: the helper is a field-level Brauer vanishing input, while the existing node is a low-degree Leray comparison theorem.
lem-sc-strict-henselian-dvr-fraction-brauer-zero vs lem-sc-open-curve-gm-direct-image-cohomology: the helper supplies one boundary input, while the existing node asserts global cohomology comparison for all q <= 2.
lem-weil-pbc-gm-strict-henselization-stalk-formula vs lem-sc-open-curve-boundary-higher-direct-image-vanishing: the helper is a general stalk-to-strict-henselization comparison for G_m, while the item is the specialized vanishing conclusion for an open curve.
lem-weil-pbc-gm-strict-henselization-stalk-formula vs lem-sc-brauer-zero: the helper is a local higher-direct-image stalk formula, while lem-sc-brauer-zero is global Brauer vanishing on a curve.
lem-weil-pbc-gm-strict-henselization-stalk-formula vs lem-sc-open-curve-etale-leray-low-degree: the helper identifies stalks with local cohomology, while the existing node derives global low-degree Leray isomorphisms from stalk vanishing.
lem-weil-pbc-gm-strict-henselization-stalk-formula vs lem-sc-open-curve-gm-direct-image-cohomology: the helper is the local stalk calculation used as an input, while the existing node is the global comparison theorem that also uses Leray.
lem-weil-pbc-gm-strict-henselization-stalk-formula vs lem-weil-pbc-sets-pushforward-stalk-strict-henselization: the existing node is degree zero for sheaves of sets; the new node identifies all higher cohomology stalks for G_m.

## Second reading by J1

Source read: /home/ubuntu/c1-stacks-review/etale-cohomology.tex, Theorem Tag 03Q9 (theorem-higher-direct-images), Lemma Tag 03RJ (lemma-higher-direct-jstar-Gm), and Lemma Tag 03RG (lemma-cohomology-Gm-function-field-curve); /home/ubuntu/c1-stacks-review/more-algebra.tex, Lemma Tag 0AP3 (lemma-henselization-dvr). The item is an adaptation of 03RJ to an open complement, not a statement in the discussion preceding 03RM. Its hypotheses are enough: the curve is Noetherian and integral, the boundary points are closed, and the strict-henselization fraction field is algebraic over the one-variable function field.

- Step 1: checked against 03Q9 and the exact unrestricted stalk-formula helper; lem-sc-smooth-connected-curve-local-rings supplies Noetherianity, and the open-immersion definition gives quasi-separatedness. Verdict: valid after adding the hypotheses and citations explicitly.
- Step 2: checked against the open-immersion and derived-direct-image definitions; on an open neighbourhood inside C, j is the identity and its positive derived images vanish. Verdict: elementary, with the argument written out.
- Step 3: checked against 03RJ, 03RG, 0AP3 and the statements of lem-sc-smooth-connected-curve-local-rings, cor-sc-hilbert-90-field, and lem-sc-brauer-algebraic-function-field-zero. The DVR has exactly generic and closed points; the strict henselization has algebraic fraction field over k(Cbar); the field theorem applies with L=E=K. Verdict: valid after replacing the unsupported general DVR Brauer assertion and citing DVR preservation.
- New node lem-weil-pbc-gm-strict-henselization-stalk-formula: checked hypothesis by hypothesis against 03Q9, theorem-higher-direct-images, first assertion, which permits an arbitrary abelian etale sheaf; G_m is a specialization. Statement only, self-contained, definition dependencies completed, source tag and label corrected, TeX escaped once. Existing prop-weil-pbc-strict-henselization-stalk-formula is torsion-only, so it cannot replace this node. Blueprint search found no equivalent. Independent Lean Finder and grep searches found no etale cohomology match; Loogle was under load on the second pass. At q=0 it gives the usual direct-image stalk formula; the empty scheme gives zero on both sides.
- New node lem-sc-strict-henselization-dvr: checked hypothesis by hypothesis against 0AP3, lemma-henselization-dvr, first and third conditions. Statement only, self-contained, definition dependencies and TeX checked. DAG tag and keyword searches and blueprint search found no equivalent; independent Lean Finder, Loogle and grep found no Mathlib declaration. For a field, neither side is a DVR; for a DVR both sides are DVRs. The empty scheme is irrelevant to this ring statement.

Changes: removed lem-sc-strict-henselian-dvr-fraction-brauer-zero, whose arbitrary strictly henselian DVR hypothesis is broader than the field theorem 03RG used by the source. Cited the existing algebraic-function-field Brauer node instead. Added the 0AP3 DVR-preservation helper, corrected the 03Q9 helper's source and missing definition dependencies, made the boundary field's algebraicity explicit, corrected the item's misleading 03RM attribution, and regenerated the verbatim step citations. The item statement was shortened to its vanishing claim; its mathematical conclusion and hypotheses were not weakened. The project's literature checkout lacks the .tex files, but the same Stacks .tex source was available at the path listed above. The first worker's review is preserved above.

Tool uses declared: lem-sc-smooth-connected-curve-local-rings supplies Noetherianity and the closed-point DVR; lem-sc-brauer-algebraic-function-field-zero supplies the algebraic-extension field vanishing. Both are statement-level black boxes absent from sk-thm-br and are used to execute, not replace, its boundary-stalk calculation.
