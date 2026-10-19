1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-finite-locally-free-multisection-connected-open.json` — item, split; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-flat-reduced-section-component-open.json` — statement-only dependency; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-finite-locally-free-composition.json` — Mathlib leaf; finite, flat, and locally finite-presentation stability under composition.
- `dag/nodes/sec-trace-formula/lem-trf-section-component-quasi-compact.json` — statement-only dependency; no Mathlib match.
- `citations.json` — verbatim statement quotes for all cited nodes and steps.

2. Attachments: none. I searched the source trees for the item tag, title, and connected-fibre terminology; no sorry-free project declaration states the item.

3. WANTED: none. The complete Stacks source is present in `literature/stacks-project/more-morphisms.tex`.

4. The returned split retained the correct Tag 057I statement. I repaired the missing base-change stability citations in step 1, finite locally free base-change and composition citations in steps 3–4, and geometric-connectedness reflection in step 6. I removed the redundant finite-locally-free topology node because existing Mathlib leaves separately give openness and closedness. The surviving new nodes now include all definition dependencies and lean-audit metadata. I searched the DAG and blueprint for duplicates; the flat geometrically reduced section-component input and affine-base quasi-compactness input are not restatements of the existing smooth or locally constructible nodes.

## Review by Q20

I reread Tag 057I, its cited Stacks lemmas, and every cited DAG statement after the repair. Step 1 cites `lem-weil-pbc-flat-morphism-base-change` and clause (3) of `lem-weil-pbc-qcqs-morphism-permanence`; geometric reducedness is checked by the iterated field-extension definition. Step 2 uses the cartesian section-component statement and the connected designated fibre exactly as stated. Step 3 derives finite-local-freeness of the self-intersection map from the existing finite, flat, and locally finite-presentation base-change leaves and the new Mathlib composition leaf; open and closed images use `lem-weil-pbc-flat-lfp-open` and `lem-weil-pbc-finite-closed-map-finite-fibres`. Step 4 checks finite-local-freeness of the induced cover before fpqc open descent. Step 5 applies the affine-base component quasi-compactness input over the affine finite cover and finite base-change permanence. Step 6 cites `lem-sbc-connected-rational-point-geometrically-connected` and `lem-weil-geometrically-connected-check-after-extension`. I verified every cited statement and hypothesis, regenerated `citations.json` from those statements, and tested empty fibres, the identity multisection, and rank-zero cases. The target statement and hypotheses are unchanged.

5. Nothing remains unfinished except the required delivery dry run and push.

## Not duplicates

- `lem-trf-finite-locally-free-composition` vs `lem-trf-finite-locally-free-multisection-connected-open`: the new leaf only states composition stability; the item constructs a descended connected-fibre open.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-smooth-section-component-open`: the new node allows flat geometrically reduced families, while the existing node assumes smoothness.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-section-component-locally-constructible`: the new node concludes openness, while the existing node concludes local constructibility.
- `lem-trf-section-component-quasi-compact` vs `lem-sbc-section-component-locally-constructible`: the new node concludes quasi-compactness over an affine base, while the existing node only gives local constructibility.
- `lem-trf-finite-locally-free-composition` vs `lem-weil-pbc-qcqs-morphism-permanence`: the new leaf combines finite, flat, and locally finite-presentation composition; the existing node only gives finite-presentation base change and qcqs permanence.
- `lem-trf-finite-locally-free-composition` vs `def-sbc-locally-finite-presentation`: the new leaf includes finite and flat composition; the existing definition only defines locally finite presentation.
- `lem-trf-finite-locally-free-composition` vs `lem-sc-constant-locus-closed`: the new leaf concerns composition of arbitrary finite locally free maps; the existing node concerns a constant-locus closed subset.
- `lem-trf-finite-locally-free-composition` vs `lem-weil-pbc-etale-morphism-open-map`: the new leaf concerns finite locally free composition, including non-étale maps; the existing node concerns openness of étale maps.
- `lem-trf-finite-locally-free-composition` vs `lem-sbc-finite-etale-generic-fibre-cover-density`: the new leaf has no étale generic-fibre cover or density hypothesis.
- `lem-trf-finite-locally-free-composition` vs `lem-sbc-finite-etale-generic-fibre-hom-extension-existence`: the new leaf is a permanence statement, while the existing node is an extension-existence theorem.
- `lem-trf-finite-locally-free-composition` vs `lem-sbc-flat-quasi-finite-smooth-local-dimension`: the new leaf is composition stability, while the existing node is a local dimension statement.
- `lem-trf-finite-locally-free-composition` vs `lem-sbc-generic-closed-subset-fibre-nonempty`: the new leaf concerns morphism composition, while the existing node concerns nonempty fibres after shrinking.
- `lem-trf-finite-locally-free-composition` vs `lem-sbc-generic-fibre-incidence-spread`: the new leaf has no generic-fibre incidence data.
- `lem-trf-finite-locally-free-composition` vs `lem-sbc-geometric-generic-cover-spread`: the new leaf has no geometric-cover spreading conclusion.
- `lem-trf-finite-locally-free-composition` vs `lem-sbc-smooth-connected-generic-geometry-core`: the new leaf has no smooth connected-generic-fibre hypotheses.
- `lem-trf-finite-locally-free-composition` vs `lem-sbc-smooth-connected-generic-geometry-stalk-iso`: the new leaf has no stalk comparison.
- `lem-trf-section-component-quasi-compact` vs `lem-trf-finite-locally-free-multisection-connected-open`: the new node concludes quasi-compactness of a section component over an affine base; the item descends an open through a finite locally free multisection.
- `lem-trf-section-component-quasi-compact` vs `lem-sbc-affine-section-noetherian-descent`: the new node concludes quasi-compactness; the existing node constructs a noetherian affine model.
- `lem-trf-section-component-quasi-compact` vs `lem-sbc-section-component-generic-dichotomy`: the new node concludes quasi-compactness; the existing node gives a generic dichotomy.
- `lem-trf-section-component-quasi-compact` vs `lem-sbc-section-component-noetherian-model`: the new node concludes quasi-compactness; the existing node supplies noetherian model data.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-affine-section-noetherian-descent`: the new node gives openness for flat geometrically reduced families over arbitrary bases; the existing node descends an affine section to a noetherian model.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-section-component-generic-dichotomy`: the new node concludes global openness; the existing node gives only a generic dichotomy.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-smooth-section-component-generalization`: the new node allows flat geometrically reduced families; the existing node assumes smoothness and proves generalization stability.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-smooth-section-component-noetherian-generalization-core`: the new node is global openness; the existing node is a noetherian smooth generalization core.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-smooth-section-component-noetherian-generalization`: the new node has no noetherian smoothness hypothesis.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-smooth-section-component-noetherian-model-data`: the new node concludes openness; the existing node constructs noetherian model data.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-smooth-section-component-noetherian-model`: the new node concludes openness; the existing node supplies a noetherian model.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-smooth-trait-section-components`: the new node applies to arbitrary flat geometrically reduced families; the existing node compares components over a trait.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-pointed-smooth-family-stage`: the new node does not assume a pointed smooth-family stage.
- `lem-trf-flat-reduced-section-component-open` vs `lem-sbc-section-component-noetherian-model`: the new node states the openness theorem itself, while the existing node only constructs a noetherian model used in its proof.
