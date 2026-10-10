Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-picard-locus-closed.json` — repaired four-step valuation proof.
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-locus-closed-valuation-criterion.json` — statement-only Stacks 02JQ/01R8 node; no Mathlib exact match.
- `dag/nodes/sec-abelian-varieties/lem-sc-picard-locus-closed-valuation-triviality.json` — statement-only Stacks 0EX8 node; no Mathlib exact match.
- `citations.json` — verbatim dependency quotes for every step.

Attachments: none.

WANTED: none.

What was wrong: the returned version had a single circular step applying Tag 0BF0, which is the item's own conclusion. I replaced it with the valuation-ring proof and added the two missing non-elementary statement nodes requested by the return.

## Not duplicates

lem-sc-picard-locus-closed-valuation-criterion vs lem-weil-pbc-scheme-image-qc-kernel: the existing node states the scheme-theoretic image's affine-kernel universal property, while this node states the valuative specialization criterion that makes the image topologically closed.
lem-sc-picard-locus-closed-valuation-criterion vs lem-weil-pbc-scheme-theoretic-image-proper: the existing node proves properness and closedness of a scheme-theoretic image under a proper morphism, while this node handles a quasi-compact immersion using valuation probes.
lem-sc-picard-locus-closed-valuation-criterion vs def-nagata-dense-valuation-probe: the existing definition is a valuation probe for a point in an affine target's scheme-theoretic image, while this node gives the global closed-image criterion for an immersion and all valuation-ring maps to the target.

## Review by J1

I reread the item's Tag 0BF0 source and the universal-property statement in `lem-sc-picard-diagonal-locally-closed`. Step 1 now uses that node only for finite-presentation immersion and uses the new 02JQ/01R8 node for the valuation test. Step 2 checks that flatness, properness, finite presentation, and geometric integrality survive base change, derives the generic global-sections equality from the universal pushforward hypothesis, and uses the diagonal node's factorization property plus triviality of the Picard group of a field to trivialize the generic fibre. Step 3 quotes exactly the new 0EX8 node. Step 4 uses its universal property with `N = O_A`, then applies the closed-image criterion and the elementary fact that an immersion with closed image is a closed immersion. I checked both new nodes against their Stacks tags, searched the whole DAG and blueprint for duplicates, and ran the required msearch LeanFinder, Loogle, and grep searches; only general Mathlib specialization results were found. The prior circular direct application of Tag 0BF0 was removed.

What could not be finished: no Lean code is written at stage 1.

## Second reading by J1

- Item statement: checked against More on Morphisms, Lemma `lemma-get-a-closed`, Tag 0BF0; hypotheses and conclusion agree.
- Step 1: checked against Tag 0BDP and Morphisms Lemmas `morphisms-lemma-reach-points-scheme-theoretic-image` (02JQ) and `morphisms-lemma-quasi-compact-scheme-theoretic-image` (01R8); cited statements supply the needed immersion and valuation criterion.
- Step 2: checked against Tag 0BDP and the Tag 0BF0 proof; base change preserves the listed hypotheses, universal pushforward gives the generic global-sections equality, and the Picard group of a field is trivial.
- Step 3: checked against More on Morphisms, Lemma `lemma-triviality-generic-fibre-valuation-ring`, Tag 0EX8; all valuation-ring, generic-fibre, closed-fibre, and global-sections hypotheses are present.
- Step 4: checked against Tag 0BDP and Morphisms Tags 02JQ/01R8; factorization gives the valuation property, and an immersion with closed image is a closed immersion.
- New node `lem-sc-picard-locus-closed-valuation-criterion`: statement checked against Morphisms Lemmas `morphisms-lemma-reach-points-scheme-theoretic-image` (02JQ) and `morphisms-lemma-quasi-compact-scheme-theoretic-image` (01R8); statement-only, self-contained, definitions cited, no Mathlib exact match.
- New node `lem-sc-picard-locus-closed-valuation-triviality`: statement checked against More on Morphisms Lemma `lemma-triviality-generic-fibre-valuation-ring` (0EX8); statement-only, self-contained, definitions cited, no Mathlib exact match.

Changes made: corrected the item's `created.item` provenance, made its split blueprint metadata structured, and expanded both new-node source fields with exact Stacks labels. The circular direct application of Tag 0BF0 is absent. Small cases checked: a field valuation ring, a zero-dimensional integral fibre, and the generic fibre.
