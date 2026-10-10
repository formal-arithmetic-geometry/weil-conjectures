Files written:
- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-basechange.json` (item, split)
- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-restriction-open.json` (statement, unsplit, no Mathlib match)
- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-affine-basechange.json` (statement, unsplit, no Mathlib match)

Attachments: none.

WANTED: `literature/stacks-project/duality.tex`, Tags 0AAB, 0E4J, and 0AA8; the local literature checkout does not contain the Stacks TeX source. I checked the official Stacks pages for the exact statements and proofs.

The item was not present in the slopmaster2 Lean source and has no sorry-free declaration. I searched the DAG and blueprint for Tag 0AAB, 0E4J, 0AA8 and right-adjoint base-change wording; no duplicate node states either auxiliary result. Both auxiliary nodes are statement-only, strictly smaller than the item, and introduce their schemes, morphisms, fibre products, right adjoints, and derived categories in their own statements. The item statement and hypotheses agree with Tag 0AAB: Y and Y' are qcqs, f is proper, flat, and finitely presented, and the conclusion is the canonical isomorphism for every quasi-coherent derived K.

## Review by C1

I read Tag 0AAB (Lemma 48.12.4) and its proof. Its first step invokes Tag 0E4J (Lemma 48.12.2) to make the right-adjoint construction compatible with restriction to opens, which is exactly the statement of the first new node. Its second step invokes Tag 0AA8 (Lemma 48.6.2), whose affine case (1) gives the second new node. Step 1 of the item cites only the first auxiliary statement and uses it to reduce to affine opens. Step 2 cites only the affine statement; the additional Tor-independence hypothesis in Tag 0AA8 is met because flatness of f makes every base change Tor independent. The final gluing is the locality asserted by the restriction statement. I checked the direction of the canonical map against both the item and Tag 0AA8: it is `Lg_X^*a(K) -> a'(Lg^*K)`, equivalently the inverse orientation of the displayed isomorphism in the item. I tested the formulation on an identity base change and on an affine identity morphism, where the map is the identity. Mathlib searches for both new nodes found only generic sheaf adjunction declarations; no derived quasi-coherent proper-flat base-change theorem was found, and LeanSearch was unavailable.

## Second reading by C1

- Item statement: checked against Stacks Tag 0AAB (Lemma 48.12.4), including all hypotheses and the orientation-equivalent canonical base-change isomorphism; verdict: agrees.
- Step 1: checked against Tag 0AAB, Tag 0E4J part (2), and Remark 48.6.1; the restriction node and the step now spell out compatibility on both bases and affine-cover locality; verdict: repaired and sound.
- Step 2: checked against Tag 0AA8 hypotheses (1)--(3), case (1); flatness supplies Tor independence and finite presentation supplies the case-(1) hypothesis; verdict: repaired and sound.
- Node `lem-sc-proper-flat-right-adjoint-restriction-open`: checked hypothesis by hypothesis against Tag 0E4J part (2), with all schemes, base changes, open immersions, projections, and right adjoints introduced; verdict: repaired and self-contained.
- Node `lem-sc-proper-flat-right-adjoint-affine-basechange`: checked against Tag 0AA8, affine case (1), including map direction; affine identity and field-base cases give the identity map; verdict: agrees and is a strict auxiliary specialization.

Changes made: expanded the restriction node to cover restrictions on either base and defined every symbol used; rewrote both proof steps to include locality and Tor-independence arguments; corrected the item's erroneous `created.item` metadata; replaced auxiliary-node search records with searches actually run by `msearch.py`; updated the verbatim citation quote for step 1. No source error was found.
