1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-relative-kill-by-twisting.json`: statement node, no new child nodes, Mathlib search verdict no match.
- `citations.json`: verbatim citations for every non-elementary proof step.

2. Attachments: none.

3. WANTED: none.

4. The imported node was unsplit and had no proof. I kept its statement and source (Stacks Cohomology of Schemes, Lemma 30.17.1, Tag 02O1). I checked the whole DAG for the Tag 02O1 statement and found `lem-weil-pbc-coherent-serre-vanishing`, which is only the affine-base specialization and is cited as such; it is not a duplicate of the relative statement. No new node was necessary because all proof ingredients already exist as DAG nodes.

## Review by C1

I read the item source and the existing affine specialization `lem-weil-pbc-coherent-serre-vanishing`. Step 1 uses `lem-pc-proper-base-change` for properness after restricting to an affine base open and then applies the affine specialization; its Noetherian, coherence, and ampleness hypotheses are exactly the restrictions of the item's hypotheses. Step 2 uses `lem-pc-cohomology-sections-affine-base`, whose statement identifies affine-base sections of the higher direct image with cohomology, `lem-pc-finite-support-hi` (1), which states quasi-coherence of higher direct images, and `lem-weil-pbc-affine-tilde-gamma-adjunction` (3), whose counit is an isomorphism for quasi-coherent sheaves; together these imply the restricted higher direct image is zero. Step 3 uses the exact statement of `lem-pc-restrict-derived-direct-image-open` to identify the restriction of `Rf_*` with the derived image over the affine open, and hence its cohomology sheaf with the zero sheaf from Step 2. Step 4 is the elementary finite-affine-cover maximum and sheaf-locality argument. I checked the empty sheaf and zero module cases: every cited vanishing statement gives the zero sheaf immediately, and the bound argument remains valid. The Mathlib searches were run for the item; LeanSearch was unavailable, while LeanFinder, Loogle, and grep found no relative Serre-vanishing declaration.

## Not duplicates

lem-pc-relative-kill-by-twisting vs lem-weil-pbc-coherent-serre-vanishing: the existing node assumes an affine Noetherian base and absolute ampleness, whereas this item assumes a Noetherian scheme base, relative ampleness on every affine base open, and concludes vanishing of the higher direct-image sheaves.

## Second reading by C1

- Step 1 checked against Stacks Tag 02O1's finite-affine-base reduction and the statements of `lem-pc-proper-base-change`, `def-weil-proper-morphism`, and `lem-weil-pbc-coherent-serre-vanishing`; verdict: correct after making the proper-to-quasi-compact/quasi-separated hypotheses explicit.
- Step 2 checked against Tag 02O1's affine comparison and the statements of `lem-pc-cohomology-sections-affine-base`, `lem-pc-finite-support-hi` (1), and `lem-weil-pbc-affine-tilde-gamma-adjunction` (3); verdict: cited statements supply the claimed vanishing.
- Step 3 checked against Tag 02O1's passage from affine restrictions to higher direct images and `lem-pc-restrict-derived-direct-image-open`; verdict: restriction and cohomology-sheaf identification are valid.
- Step 4 checked against Tag 02O1's finite affine cover conclusion; verdict: finite maximum and sheaf locality are elementary and sufficient.
- The item statement was checked hypothesis by hypothesis against Cohomology of Schemes Lemma 30.17.1 (Tag 02O1); verdict: agrees, including relative ampleness expressed through affine base opens.
- No new child nodes exist; therefore B1--B7, duplicate checks, and Mathlib-leaf checks are vacuous. Existing cited nodes were searched in `dag/nodes` and their statements opened.
- Small cases checked: empty scheme, zero sheaf, a field base, and n = 0 or 1; all give the stated zero conclusions or are covered by the eventual bound.

Changes made: added the proper-morphism definition citation and its verbatim citation quote; rewrote the final step to use an explicit finite affine cover and maximum, removing the unsupported affine-neighborhood wording.

