Files written:
- `dag/nodes/sec-picard-framework/lem-pc-affine-flat-module-local-criterion.json` (split item)
- `dag/nodes/sec-picard-framework/lem-pc-affine-flat-module-localization-preserves-flatness.json` (statement-only unsplit node; no Mathlib exact match)
- `citations.json`

Attachments:
- None.

WANTED: `literature/stacks-project/algebra.tex`, Algebra Lemma 10.39.18, Tag 00HT, because the imported literature checkout is not present on this machine.

The source node had no Lean declaration in the source checkout. I checked the source tree by item id and by the flatness/localization terminology. The new node is strictly broader than the item: it allows an arbitrary multiplicative subset of A and concludes flatness over R before the prime-local base change. I searched the whole DAG and found the existing Mathlib leaf `lem-weil-pbc-flat-over-localization` for the second step, so I did not create a duplicate. The searches for the new node found only localization over a submonoid of the base ring (`Module.Flat.of_isLocalizedModule`), not localization in an algebra, and LeanSearch was unavailable.

## Review by C1

I checked the item statement against the imported Tag 00HT description and retained its hypotheses: a ring map R -> A, an A-module M flat over R, and q with p its contraction. In step 1 the cited new statement supplies exactly flatness of the localization at A\\q over R; I separately checked that r outside p maps outside q, so the R_p-module structure is defined. In step 2 the cited existing node states the needed iff for a module over a localization, and I apply its reverse direction with A = R and A' = R_p. The small edge case q = top cannot occur for a prime, while for q = (0) in a domain the argument reduces to ordinary fraction-field localization. I also checked that no source declaration or existing DAG node states the new algebra-localization lemma.

## Not duplicates

lem-pc-affine-flat-module-localization-preserves-flatness vs lem-pc-affine-flat-module-local-criterion: the new statement allows an arbitrary multiplicative subset of A and concludes flatness over R; the item specializes to A\\q and then changes the base to R_p.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-sc-p1-localization-short-exact: the existing node concerns exactness of a short sequence under localization, not flatness of a localized A-module over a distinct base R.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-pc-affine-sections-flat-over-base: the existing node is the converse local criterion (prime-local flatness implies global flatness), while the new node is preservation under algebra localization.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-regular-local-maximal: the existing node concerns regular local rings and maximal ideals, not module flatness under localization.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-localization-flat: the existing node says a localization ring map is flat; the new node concerns an arbitrary flat module localized in an algebra.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-localization-regular: the existing node concerns preservation of regular elements under localization, not flat modules.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-flat-local-ring-maps: the existing node concerns flat maps between local rings, not localization of modules over an arbitrary base.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-flat-map-local-criterion: the existing node is the local criterion for flat ring maps, whereas the new node is module flatness after localizing an A-module.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-regular-through-localization: the existing node transports regularity through localization, not flatness.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-weakly-regular-sequence-localization-prime: the existing node concerns weakly regular sequences under prime localization, not arbitrary modules.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-annihilator-localization-finite: the existing node concerns annihilator finiteness under localization, not flatness.
lem-pc-affine-flat-module-localization-preserves-flatness vs lem-weil-pbc-flat-over-localization: the existing node compares flatness over a ring and its own localization for a module already over the localized ring; the new node localizes an A-module while retaining flatness over a different base R.

## Second reading by C1

- Item statement: checked against Stacks Algebra Lemma 10.39.18, Tag 00HT, clause (6), only-if direction; the ring-map, A-module, prime q, contraction p, and localized flatness hypotheses and conclusion agree exactly.
- New node `lem-pc-affine-flat-module-localization-preserves-flatness`: checked against the localization argument in Tag 00HT (00HT, proof of clause (6)); arbitrary multiplicative-set localization of an R-flat A-module remains R-flat, with the induced R-action, and the statement is strictly smaller than the item.
- Item step 1: the new node gives R-flatness after localizing by A\\q; the assertion that elements of R\\p map outside q and become units in A_q is immediate from the definitions, so the R_p-module structure is valid.
- Item step 2: checked against `lem-weil-pbc-flat-over-localization`; its stated equivalence applies to the R-module R_p-module structure and gives precisely flatness over R_p.
- Edge cases: q=(0) in a domain reduces to fraction-field localization; q cannot be top; zero modules and zero rings satisfy both flatness statements vacuously.
- Existing-node and Mathlib searches: checked the whole DAG for the new node's localization-over-an-algebra fact and reran the recorded semantic and source searches; no exact declaration or duplicate was found.

Changes made: none to the mathematics or node statements. Added this second-reading section and recorded the source-label/edge-case audit; the source checkout lacks the imported `.tex`, so Tag 00HT was verified from the current Stacks HTML entry.
