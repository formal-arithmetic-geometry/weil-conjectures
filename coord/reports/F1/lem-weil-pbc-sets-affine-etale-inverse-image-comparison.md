Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sets-affine-etale-inverse-image-comparison.json`: item, statement split into three proof steps; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-affine-etale-site-base-change.json`: new statement-only node; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node at every step.

Attachments: none.

WANTED: none.

The item had no sorry-free or sorry-bearing declaration in `WeilConjectures`; its Lean audit is therefore unchanged at `none`. The existing DAG already supplied the affine-site topos equivalence, set-valued inverse-image adjunction uniqueness, étale base-change continuity, and composition-unit statements. I added only the generic affine-site base-change morphism statement, which is strictly narrower than the item's comparison theorem.

## Review by F1

I read the item source, the Stacks Etale Cohomology proof of Tag 09YQ, and Topologies Tag 04HR. I also read the complete statements of every cited node. Step 1 uses the new node, whose statement explicitly says that affine base change is well defined, continuous, and induces the site morphism. Step 2 uses the affine-etale topos equivalence, the base-change continuity/direct-image formula, and the adjoint-uniqueness lemma; those statements provide exactly the restriction equivalences, the equality of restricted direct images, and uniqueness of the left adjoint used in the comparison. Step 3 uses clauses (0) and (1) of the composition-units node, which state the section restriction formula and compatibility with canonical iterated fibre-product identifications. I checked the affine hypotheses at every use: an affine morphism base-changes affine objects to affine objects, and the standard coverings are finite and remain standard. I checked the empty and identity cases are covered by the same unit and universal-property formulas. The original item was unsplit with no proof; the correction was to add the one generic base-change node and make all three proof steps cite statements that contain their claimed facts.

The blueprint reference remains the imported ancestor `lemma-weil-pbc-proper-strict-henselian-h0`; the steps realize its clause comparing inverse images after affine-site restriction.

What could not be finished: no Lean compilation is permitted at stage 1, and no Lean declaration for this item exists to attach.
