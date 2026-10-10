# Delivery report

Files written:

- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-direct-sums.json` (item, split; no Mathlib match).
- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-perfect-direct-image-perfect.json` (statement-only dependency; no Mathlib match).
- `citations.json` (verbatim citation quotes for every proof-step use).

Attachments: none.

WANTED: Stacks Project `more-morphisms.tex`, Tag 0B6G, for the perfect direct-image prerequisite.
WANTED: Stacks Project `duality.tex`, Tag 0E4H (Lemma 48.12.1), for the direct-sum theorem and its proof.

The Lean source trees contain no declaration tagged `(blueprint: lem-sc-proper-flat-right-adjoint-direct-sums)` and no sorry-free declaration matching the item. The imported local Stacks literature is absent, so the proof follows the Tag 0E4H argument from the node's source citation and is marked `proof_origin.by = agent`. The existing perfect-direct-image node is Noetherian/perfect-morphism-only, so it cannot be applied directly to the item's qcqs proper-flat-finite-presentation hypotheses; I created the precise statement-only prerequisite instead. The item proof has three steps: perfect direct images plus compactness; the adjunction Hom calculation; and perfect generation applied to the cone of the canonical sum map.

## Review by F1

I read the item node, its ancestor reference to `lem-sc-finite-duality`, and the neighboring nodes `lem-pc-perfect-object-compact` and `lem-pc-derived-qcoh-perfect-generation`. The new prerequisite introduces Y, f, and P itself and states exactly the perfect direct-image fact used in Step 1, with all proper, flat, finite-presentation, qcqs, and perfectness hypotheses explicit. Step 1 uses only that statement and the compactness statement, which explicitly gives the Hom/direct-sum isomorphism. Step 2 uses the same two statements: the right-adjoint Hom bijections are the definition of a right adjoint, and compactness supplies the direct-sum comparison. Step 3 uses the stated perfect-generation closure under shifts, cones, retracts, and arbitrary direct sums; the cone argument then forces the canonical map to be an isomorphism. I checked the edge cases of an empty index family (the zero map) and a singleton family (the identity comparison), and the argument specializes to the identity proper flat morphism. Mathlib searches were run for both the item and the new prerequisite with LeanFinder, Loogle, source grep, and LeanSearch; LeanSearch was unavailable and recorded as such.

## Not duplicates

`lem-sc-proper-flat-perfect-direct-image-perfect` vs `lem-pc-proper-perfect-direct-image-perfect`: the existing node assumes Noetherian schemes and a perfect proper morphism, while the new node assumes only a quasi-compact quasi-separated base and a proper flat morphism of finite presentation, so the existing statement does not cover the new hypotheses.

## Second reading by F1

- Item statement: checked against the Tag 0E4H title and hypotheses as recorded in the blueprint; qcqs base, proper flat finite-presentation morphism, quasi-coherent derived categories, and a right adjoint are all present; edge cases include the empty and singleton coproducts and the identity morphism.
- New node `lem-sc-proper-flat-perfect-direct-image-perfect`: checked against Tag 0B6G as specialized to proper flat finite-presentation morphisms; its objects and perfectness conclusion are self-contained, and the existing `lem-pc-proper-perfect-direct-image-perfect` was rejected as a narrower Noetherian/perfect-morphism statement. Mathlib searches are recorded in the node.
- Step 1: checked that the cited direct-image-perfect statement supplies perfectness of `Rf_*P` and that `lem-pc-perfect-object-compact` applies on `Y`; the canonical Hom direct-sum comparison follows exactly.
- Step 2: checked the adjunction identifications and the direction of the canonical map `u`; expanded the calculation to use compactness of both `P` and `Rf_*P`, with Step 1 supplying the latter. It is now correctly marked non-elementary.
- Step 3: checked the cone argument against perfect generation: the Hom-orthogonal class is closed under shifts, cones, retracts, and coproducts, contains perfects, hence contains the cone; the zero identity implies `C=0`.

Changes made: added the existing `def-sbc-locally-finite-presentation` definition dependency to the item and its prerequisite, and expanded Step 2 to state the canonical map and both compactness comparisons explicitly. No source files were available locally beyond the recorded wanted Tags 0B6G and 0E4H, so the source comparison uses the imported blueprint citations and node statements.
