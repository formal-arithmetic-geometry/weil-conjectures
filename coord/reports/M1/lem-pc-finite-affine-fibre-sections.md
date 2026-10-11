Files written:

- `dag/nodes/sec-picard-framework/lem-pc-finite-affine-fibre-sections.json`: item split into three proof steps; no new nodes.
- `citations.json`: citation for the existing affine fibre-product statement.

Attachments: none.

WANTED: none.

The item was not already stated by a project declaration in either source checkout. I read the imported item and its blueprint ancestor `lem-pc-flf-properties`, and checked the relevant source description, Stacks Tag 02KB (lemma-finite-flat, affine calculation). The statement already has the required affine hypotheses and dependencies. The first step expands the direct-image sections on basic opens and the stalk colimit; the second is the elementary localization and quotient tensor calculation; the third uses the existing node `lem-weil-pbc-fibre-product-affine-spectra`, whose statement explicitly gives the affine fibre product and its global-sections ring. I checked that the cited node says exactly the global-sections conclusion used in step 3. No hypotheses are added: finiteness is part of the item but the affine calculation only uses the displayed affine presentations. Small cases checked were `B=A` (identity morphism), `B=0`, and `s` corresponding to a maximal ideal, where the result reduces to the usual residue-field tensor calculation.

## Review by M1

I read the item source and the parent blueprint paragraph in full. For step 1, the calculation is the definition of direct image on the affine basic opens followed by the stalk colimit, so it is marked elementary and uses no hidden theorem. For step 2, the identification of the residue field with `A_s / m_s A_s` and the associativity of tensor products are elementary ring manipulations. For step 3, I opened `lem-weil-pbc-fibre-product-affine-spectra.json`; its statement says that the affine fibre product is `Spec(A tensor_R B)` and, in particular, that its global sections are that tensor product, exactly the fact used. I verified the object ordering by taking the base ring to be `A` and the second algebra to be `kappa(s)`. I searched the whole DAG and blueprint for duplicate fibre-section or affine stalk statements and found none. Mathlib searches were run for the item with LeanFinder, Loogle, and grep; LeanFinder returned only generic fibre/tensor APIs, Loogle had no exact hit, and grep returned general affine global-sections declarations but no theorem for this canonical isomorphism, so the item is not marked as a Mathlib leaf. No source or statement correction was needed.
## Second reading by M1

- Item statement: checked against the imported `lem-pc-flf-properties` affine clause and Stacks Tag 02KB (Lemma `lemma-finite-flat`), hypothesis by hypothesis; all affine, point, residue-field, finite-algebra, and canonical-map data are present with no extra assumption.
- Step 1: checked against the affine direct-image and localization calculation in Tag 02KB; the basic-open section calculation and stalk colimit are elementary from the stated affine definitions.
- Step 2: checked against the residue-field definition and tensor associativity; the quotient is `A_s / m_s A_s`, including the zero-ring and arbitrary-prime cases.
- Step 3: checked against `lem-weil-pbc-fibre-product-affine-spectra`; its statement gives the fibre as `Spec (B tensor_A kappa(s))` and its global sections in the required factor order.
- New nodes: none, so there are no B1--B7 or Mathlib-leaf records to audit. The DAG search was repeated with `rg -rl`; the same-tag parent `lem-pc-flf-properties` is a different global finite-locally-free theorem, not a duplicate.
- Edge cases checked: `B=A`, the zero algebra, a field base, and maximal and generic points.

Changes made: appended this second-reading audit only; no statement, proof step, citation, or node required repair.
