Files written:

- `dag/nodes/sec-picard-framework/lem-sc-tangent-space-vector-space.json` — statement split, one unsplit dependency, Mathlib no-match.
- `dag/nodes/sec-picard-framework/lem-sc-dual-number-scheme-pushout.json` — statement-only node, Mathlib generalization but no exact match.

Attachments: none.

WANTED: literature/stacks-project/varieties.tex, Tag 0B2B source text is referenced by the imported project but is not present in this checkout; the split follows the tag citation and the copied blueprint proof.

No statement error was found. The slopmaster2 source contains only the narrower group-scheme tangent-space module instance (with sorry), not this general scheme tangent-vector statement.

## Review by F1

I checked the item against the imported Tag 0B2B statement and the unit `sk-prop-picard-jacobian-tangent`; its hypotheses introduce the field, scheme, point, residue field, dual numbers, and all maps explicitly. I searched the whole DAG and parallel node copies for an existing pushout fact before creating `lem-sc-dual-number-scheme-pushout`; none states the explicit dual-number universal property. I also searched slopmaster2 by the item id, blueprint tag, and tangent-space keywords. The only nearby declaration is `AlgebraicGeometry.tangentSpaceAt` and its group-scheme `Module` instance in `AlgebraicGeometry/Picard/Jacobian.lean`, which is not this statement and contains sorry, so no attachment applies.

Step 1 uses exactly the new node's universal-property sentence to glue the two tangent vectors; the common restriction hypothesis is supplied by membership in `T`. Step 2 uses the same pushout equality for closure under addition and the elementary fact that every scaling map fixes the closed point. Step 3 uses uniqueness from that pushout and the displayed coefficient identities in the dual-number algebra; the remaining checks are one-line elementary comparisons of restrictions. The new node is statement-only as required, and its searches include LeanFinder, Loogle, grep, and unavailable LeanSearch records. I tested the constructions at the zero tangent vector and at scalar `0` and `1`; both reduce to the constant map through `Spec κ`.
