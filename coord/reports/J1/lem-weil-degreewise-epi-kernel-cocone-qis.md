Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-degreewise-epi-kernel-cocone-qis.json` — item, statement split into three proof steps, no new nodes, no Mathlib leaf.
- `citations.json` — verbatim statement excerpts for every cited node in every step.

Attachments:

- None. I searched the slopmaster2 source for the blueprint tag and the relevant cone/kernel terminology; no sorry-free declaration states this item exactly.

WANTED:

- None.

What was wrong or incomplete in the imported node:

- The imported item had no proof. Its statement is consistent with the comparison used in the Roos-complex node. The Mathlib search found only `CochainComplex.mappingCone.quasiIso_descShortComplex`, which concerns the cone of the first map in a short exact short complex and does not directly state the kernel-to-shifted-cone comparison, so the item remains an unsplit project statement rather than a Mathlib leaf.
- No duplicate DAG node was found for the exact kernel/epimorphism statement. Existing triangle, cone, and two-out-of-three lemmas are cited as dependencies rather than copied into new nodes.

What I could not finish:

- Nothing. The dry-run checks are the remaining verification step.

## Review by J1

I read the item source context in `literature/stacks-project/derived.tex`, especially Definition 014Q (cone and shift), Lemma 0117 (degreewise short exact complexes), Lemma 014A (two-out-of-three for triangle morphisms), Lemma 0152 (distinguished triangle attached to a short exact sequence), and the split short exact sequence argument in Lemma 070M. I also read the statements of every cited DAG node: `def-sp-abelian` supplies kernels, cokernels, monomorphisms, and epimorphisms; `def-weil-abstract-derived-category` supplies complexes, quasi-isomorphisms, localization, shifts, and cone triangles; `lem-weil-pbc-complex-ses-triangle` supplies the distinguished triangle for the kernel sequence; `def-weil-triangulated-category` supplies rotation/TR3; `lem-weil-pbc-triangle-morphism-extension` supplies completion to a morphism of triangles; and `lem-sf-triangle-morphism-iso` supplies the two-isomorphism conclusion. Each citation quote in `citations.json` is copied from the cited statement.

Step 1 checks the restricted differential and the cone differential directly, so it is elementary once the complex and abelian-category definitions are in force. Step 2 checks the kernel, middle exactness, and epimorphism hypotheses degree by degree before invoking the short-exact-sequence triangle and the rotated cone triangle. Step 3 uses TR3 with identity maps on P and Q, then applies the two-isomorphism lemma; the localization definition converts the resulting isomorphism to a quasi-isomorphism. I tested the edge case f = id, where K is zero and Cone(id)[-1] is contractible, and the zero-complex case; both agree with the statement. No hypotheses were added or omitted.

## Second reading by J1

- Item statement: checked against the kernel and cone conventions in `derived.tex` (Definition 014Q and the cone construction used in Lemma 070M); the degreewise epimorphism hypothesis, shifted terms, signs, and conclusion agree, including the zero-complex and identity-map cases.
- Step 1: checked directly from the cited complex and abelian-category definitions; the restricted differential and displayed chain map are elementary.
- Step 2: checked the degreewise short exact sequence against `def-sp-abelian`, the short-exact-complex triangle node, the cone-triangle statement, and TR2; corrected the rotated-cone map description to the projection `Cone(f)[-1] -> P` and its composite with `kappa`.
- Step 3: checked the TR3 and two-out-of-three citations and the localization conclusion; the comparison morphism has identity components on `P` and `Q`, so its first component is inverted as required.
- New nodes: none; B1-B7 and duplicate-node checks are vacuous for this split, and the recorded Mathlib searches remain attached to the item’s no-leaf decision.
- Small cases: verified `f = id` (zero kernel and contractible shifted cone) and the zero complexes; both satisfy the stated comparison.

Changes made: repaired the rotated-cone map wording, made the localization-to-quasi-isomorphism step explicit, and corrected the sandbox `created.item` metadata to this item.
