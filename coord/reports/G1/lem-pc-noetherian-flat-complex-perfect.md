1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-noetherian-flat-complex-perfect.json`: statement split; no Mathlib leaf for the item.
- `dag/nodes/sec-picard-framework/lem-pc-flat-tor-criterion.json`: statement-only unsplit node; Mathlib searches found no Tor-flatness criterion.
- `dag/nodes/sec-picard-framework/lem-pc-noetherian-finite-kernels-cokernels.json`: statement-only unsplit node; Mathlib has the more general finitely generated module category abelian result, but no direct declaration recorded as a leaf.
- `citations.json`: verbatim citations for every proof-step dependency.

2. Attachments: none.

3. WANTED: none.

4. The imported proof had four paragraphs but only cited the abstract derived-category definition. I retained its inductive finite-free construction as the item proof and added citations for the three non-elementary facts it uses: Noetherian finiteness of kernels and cokernels, K-flatness of bounded-above flat complexes, and the Tor criterion for flatness. The final finite-projective conclusion cites the existing Mathlib leaf `lem-weil-pbc-finitely-presented-flat-module-projective` rather than creating a duplicate.

5. Nothing remains unfinished in the split. The project source contains no declaration tagged `(blueprint: lem-pc-noetherian-flat-complex-perfect)` and no matching sorry-free declaration.

## Not duplicates

The duplicate K-flat node was removed in favor of existing `lem-pc-bounded-above-flat-kflat` (same Tag 06YD statement).
lem-pc-flat-tor-criterion vs lem-weil-pbc-flat-module-completion-flat: the new node is the general implication from vanishing Tor_1 with every module to flatness; the existing node concerns flatness after completion and does not state this criterion.
lem-pc-flat-tor-criterion vs lem-weil-pbc-flat-tor-ideal-criterion: the new node uses Tor_1 with every module as the hypothesis; the existing node characterizes flatness using only quotients by ideals and has a different statement and hypotheses.
lem-pc-noetherian-finite-kernels-cokernels vs lem-weil-pbc-finite-presentation-quotient-fg-ideal: the new node concerns kernels and cokernels of arbitrary module maps over a Noetherian ring; the existing node concerns finite generation of one presentation kernel ideal.
lem-pc-noetherian-finite-kernels-cokernels vs lem-weil-pbc-tensor-product-finitely-presented-algebras: the new node is closure of finite modules under module kernels and cokernels; the existing node concerns finite presentation of tensor products of algebras.
lem-pc-noetherian-finite-kernels-cokernels vs lem-weil-pbc-finite-presentation-base-change-composition: the new node is a module finiteness closure result; the existing node is a base-change/composition result for finitely presented algebra maps.
lem-pc-noetherian-finite-kernels-cokernels vs lem-weil-pbc-essentially-finite-presentation-over-intermediate: the new node is about module kernels and cokernels; the existing node concerns essential finite presentation of ring maps through an intermediate algebra.
lem-pc-noetherian-finite-kernels-cokernels vs lem-weil-pbc-finite-presentation-over-finite-type-algebra: the new node is closure of finite modules under kernels and cokernels; the existing node concerns finite presentation of an algebra over a finite-type algebra.

## Review by G1

I read the item blueprint and the surrounding unit record, then checked the project source for the blueprint tag and the relevant derived-category, flat-complex, and perfect-complex declarations. The item statement now explicitly cites its definitions. Step 1 uses only the derived-category notion of representative and cohomology. Step 2 follows the stated descending finite-free construction and cites the exact Noetherian kernel/cokernel finiteness statement; the cone cycles and stabilization remain explicit in the step. Step 3 cites existing `lem-pc-bounded-above-flat-kflat` and the derived-category localization statement for the derived tensor and Tor calculation. Step 4 cites the exact Tor-flatness criterion and the existing statement that a finitely presented flat module is finite projective; its finite-presentation hypothesis is immediate from the displayed cokernel of finite free modules. I checked the new statements on zero complexes, zero modules, and finite free modules, and searched the whole DAG and blueprint for duplicates before creating them. The recorded Mathlib searches were run for the item and cover K-flatness, Tor-flatness, and Noetherian finite-module closure; unavailable LeanSearch responses are recorded as unavailable in the search log rather than as matches.

## Second reading by G1

- Item statement: checked against the blueprint and cited definitions; verdict: agrees and is now self-contained.
- Step 1: checked against `def-weil-abstract-derived-category`; verdict: elementary.
- Step 2: checked against `def-weil-abstract-derived-category` and `lem-pc-noetherian-finite-kernels-cokernels`; verdict: dependencies match the construction.
- Step 3: checked against existing `lem-pc-bounded-above-flat-kflat` and `def-weil-abstract-derived-category`; verdict: duplicate removed and citation retargeted.
- Step 4: checked against `lem-pc-flat-tor-criterion` and `lem-weil-pbc-finitely-presented-flat-module-projective`; verdict: dependencies match.
- `lem-pc-flat-tor-criterion`: checked against Stacks Tag 00M5; verdict: self-contained prerequisite.
- `lem-pc-noetherian-finite-kernels-cokernels`: checked against Stacks Tag 00F4; verdict: self-contained prerequisite.
- Changes: removed duplicate K-flat node, updated step 3 and citations, added statement definition references, and recorded this review.
