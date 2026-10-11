Files written:

- `dag/nodes/sec-abelian-varieties/lem-sp-ce-compatible-homotopy-assembly.json` (statement, split; no new nodes; Mathlib search found no assembly theorem).
- `citations.json` (two citations of the existing acyclic-to-injective null-homotopy node).

Attachments: none.

WANTED: none.

## Not duplicates

`lem-sp-ce-compatible-homotopy-assembly` vs `lem-sp-ce-vertical-nullhomotopy`: the latter applies this assembly as an induction step to boundary/cycle rows and concludes a double-complex vertical homotopy; this item is the short-exact-sequence assembly lemma itself.

## Review by G1

I read the item source in `literature/stacks-project/derived.tex`, Tag 015I, together with the cited Weibel Homological Algebra Lemma 5.7.10 route, and read the existing node `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` in full. The first proof step uses exactly that node's assertion that every map from an acyclic complex to a bounded-below complex of injectives is chain-homotopic to zero; adjoining the augmentation object in degree -1 turns each augmentation-zero map into that situation. The degreewise extensions across `i` and splittings of `rho` use only the injectivity in `def-sp-injective-resolutions` and the displayed short exact sequences, so they are elementary once those hypotheses are in scope. Step 2 checks both defect restrictions: `E i = 0` follows from the prescribed cycle homotopy, and `rho E = 0` follows from the boundary homotopy; exactness then gives the stated factorization. Step 3 uses the same cited null-homotopy statement on the factored defect and verifies the correction preserves both compatibility equations because `pi i = 0` and `rho j = 0`. I checked the degree-zero conditions and the augmentation-zero hypotheses, and corrected the initially empty proof by making the defect factorization and the two null-homotopy applications explicit. I also searched the whole DAG and blueprint; no node states this assembly theorem, and the existing vertical-nullhomotopy node is a consumer rather than a duplicate.

What was wrong in the imported node: it had no proof or proof dependencies despite being used by the vertical-nullhomotopy node. I supplied the complete assembly argument and recorded the exact dependency quotes.

What I could not finish: nothing.

## Second reading by G1

- Item statement: checked against Stacks `derived.tex`, Tag 015I (`lemma-cartan-eilenberg`) and the compatible boundary/cycle exact-sequence construction; all source, target, augmentation, exactness, injectivity, compatibility, and degree-zero hypotheses are present. Verdict: sound.
- Step 1: checked the degreewise extensions and sections against injectivity and the displayed short exact sequences, and checked the augmented exact-complex application against `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`; the implication `R_I epsilon_I = 0` gives `R_B epsilon_B = 0` by augmentation compatibility. Verdict: sound.
- Step 2: checked `E i = 0` and `rho E = 0` from the two homotopy identities, and the factorization `E = j E' pi` from exactness; the augmentation-zero conclusion uses monicity of `j`. Verdict: elementary and sound.
- Step 3: checked the second null-homotopy application and the correction `s_I = t + j k pi`; `pi i = 0` and `rho j = 0` preserve both compatibility equations. Verdict: sound.
- Step 4: checked the degree-zero conclusion directly from the selected homotopies. Verdict: elementary and sound.
- Existing dependency node: read `lem-weil-pbc-acyclic-map-to-injective-nullhomotopy`; its statement exactly supplies the two null-homotopy uses. Verdict: citation sound.
- New-node form: statement-only split node, self-contained abelian-category, exact-sequence, augmentation, and injective-resolution hypotheses, TeX notation, Stacks/Weibel source, blueprint fields, and recorded Mathlib searches. Verdict: compliant.
- Small cases: zero complexes and concentrated degree-zero exact sequences reduce to zero defects and zero homotopies; the field case is an abelian-category instance and introduces no extra hypothesis. Verdict: consistent.

Changes made: corrected `created.item` to this item (it incorrectly named the consumer `lem-sp-ce-vertical-nullhomotopy`); no mathematical proof text or citations required alteration.
