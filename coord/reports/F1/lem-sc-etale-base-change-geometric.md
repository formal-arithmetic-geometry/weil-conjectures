1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-etale-base-change-geometric.json`: split statement; Mathlib stability leaf plus local faithfully-flat descent child.
- Existing Mathlib-backed node `lem-weil-pbc-etale-scheme-base-change` supplies the base-change direction; its Mathlib declaration is `AlgebraicGeometry.Etale.etale_isStableUnderBaseChange` at `Mathlib/AlgebraicGeometry/Morphisms/Etale.lean:74-75`.
- `dag/nodes/sec-abelian-varieties/lem-sc-etale-faithfully-flat-local.json`: unsplit statement-only child; no Mathlib match.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof. I kept its statement and filled the two proof directions. The forward direction uses the exact Mathlib base-change stability declaration. The reverse direction is isolated as a strictly affine-local descent statement, because the field-extension stalk map is faithfully flat and Tags 02VN, 02VM, 036N provide the descent of flatness, unramifiedness, and local finite presentation. Searches found no existing DAG node stating this local field-extension reflection result and no Mathlib theorem for it.

## Review by F1

I read the item source references in Varieties Tag 0C4Y and Descent Tags 02VN, 02VM, and 036N, and checked that the item hypotheses are exactly a field extension, a morphism of schemes, and a point above the chosen point. Step 1 cites the existing node `lem-weil-pbc-etale-scheme-base-change`; its statement gives exactly stability of etaleness under arbitrary base change, so the base-changed etale neighbourhood gives the pointwise conclusion. Step 2 cites the new local descent statement verbatim; its hypotheses match the item and it packages the faithfully flat local-ring argument from 0C4Y and the fpqc-local criteria 02VN/02VM/036N. I checked the underlying Mathlib source declaration at lines 74-75 and recorded it in the existing node. Small cases (identity extension, identity morphism, and an empty source neighbourhood) are consistent with both directions. `citations.json` quotes the exact statement text used by each step.

## Not duplicates

lem-sc-etale-faithfully-flat-local vs lem-sc-etale-base-change-geometric: the child is the reverse-direction local descent lemma used as a proof step, while the item is the two-way pointwise equivalence.
lem-sc-etale-faithfully-flat-local vs lem-galois-fpqc-descend-unramified: the child concerns etaleness at one point after a field extension; the existing node concerns global unramifiedness under an arbitrary fpqc covering.
lem-sc-etale-faithfully-flat-local vs lem-galois-fpqc-descend-etale: the child assumes etaleness only at a chosen point upstairs and concludes etaleness at the chosen point downstairs; the existing node assumes every base-change morphism is globally etale and concludes global etaleness.

## Second reading by F1

I checked the item against Varieties Tag 0C4Y and Descent Tags 02VN, 02VM, and 036N in the Stacks sources. The statement has the required field-extension, scheme-morphism, base-change, and point hypotheses, and its two directions agree with the source criteria. Step 1 uses the exact statement of `lem-weil-pbc-etale-scheme-base-change`; the open-neighbourhood base change is the elementary pointwise specialization. Step 2 uses the exact child statement; its local-ring hypothesis is Tag 0C4Y and its flat, unramified, and finite-presentation descent criteria are Tags 02VN, 02VM, and 036N. No uncited non-elementary fact remains.

The child node is self-contained, statement-only, cites all definition nodes, records the Stacks tags and four Mathlib searches, and is strictly smaller than the item. I tested the item and child on the identity field extension, an identity morphism, an empty source, and the zero-dimensional point case; all reduce to the expected equivalence. I removed the child blueprint `via` back-edge because it introduced a metadata cycle through the item. The existing item's maintainer metadata, including its historical `created.item`, is left unchanged for the delivery tool to preserve.
