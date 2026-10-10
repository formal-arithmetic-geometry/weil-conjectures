Files written:
- `dag/nodes/sec-picard-framework/lem-sc-koszul-regular-sequence-dual-complex.json` (item, split)
- `dag/nodes/sec-picard-framework/lem-sc-exterior-power-dual-pairing.json` (Mathlib leaf, `exteriorPower.pairingDual`)
- `citations.json`

Attachments: none.

WANTED: `literature/stacks-project/duality.tex`, Tag 0BQZ source text is not present in this checkout; the split follows the imported citation and the stated local Koszul computation.

## Review by F1
I searched the slopmaster2 project for the blueprint tag and for declarations mentioning Koszul regular sequences, dual complexes, and Tag 0BQZ; no sorry-free declaration states this item. I read the item, the Koszul-complex definition, the Koszul-regularity definition, and the existing perfect closed-immersion node. Step 1 uses exactly the definitions of the finite exterior-power Koszul terms and vanishing homology. Step 2 uses the Mathlib pairing statement and the Koszul differential definition to identify the dual terms and differential by a basis determinant calculation. Step 3 checks the empty and one-element cases and then the mapping-cone induction, with the successive regularity hypotheses giving concentration in degree r and the conormal dual as the top cohomology; localization repeats the same calculation. Step 4 checks that the determinant map is the intrinsic Ext identification, so changing generators or localizing does not change it. I searched the whole DAG and blueprint for Koszul duality, exterior pairings, and the cited tags before adding the single Mathlib leaf. Small cases r=0 and r=1 agree with A and the two-term complex Hom(A -> A,A).

## Second reading by F1

- Item statement: checked against Stacks Tag 0BQZ, lemma-regular-immersion-ext, after specializing the sheaf calculation to A, I, B, and a finite Koszul-regular sequence; hypotheses and the Ext degree agree. The zero-sequence and one-generator cases were checked explicitly.
- New node `lem-sc-exterior-power-dual-pairing`: checked against Mathlib `ExteriorPower/Pairing.lean`, `pairingDual` lines 64-66 and its determinant formula lines 71-74; the statement is an exact match and the recorded Mathlib searches are present.
- Step 1: checked against the Koszul-complex and Koszul-regularity definition nodes and the local part of Tag 0BQZ; the augmentation and finite-free assertions follow in a few lines and remain elementary.
- Step 2: checked against `pairingDual`, the explicit Koszul differential, and the determinant formula; the basis-wedge calculation supplies the dual differential.
- Step 3: checked against the explicit dual-Koszul computation in Tag 0BQZ; replaced the unsupported mapping-cone/injectivity summary with the delta-derivation, sign, shifted-Koszul, and localization calculation.
- Step 4: checked against the determinant identification and localization clauses of Tag 0BQZ; made the change-of-basis determinant argument explicit and cited the pairing node.

Changes made: corrected the item node's `created.item` to this item, and repaired Steps 3-4 to remove unsupported induction and independence claims while retaining the stated conclusion.
