## Worker report

1. Files written: item `lem-weil-pbc-derived-open-restriction` (statement, split, no new nodes); `citations.json`.
2. Attachments: none.
3. WANTED: none.
4. The imported proof had an underspecified identification of the open etale site with a localized slice and did not cite the exact extension-by-zero adjunction/exactness statement. I repaired the three steps to cite existing nodes and made the sectionwise equality, Hom argument for injectives, and derived-resolution comparison explicit. No new node was created because the DAG already contains each required fact.
5. No unfinished work.

## Review by NA

I read the target statement and its blueprint proof in `literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/lem-weil-pbc-derived-open-restriction.md`, and checked the direct-image and inverse-image definitions in their existing DAG nodes. Step 1 uses the direct-image fibre-product formula and the existing inverse-image/restriction comparison; these statements explicitly give the evaluated fibre product and the natural restriction isomorphism. Step 2 uses the existing etale-site localization equivalence, exact inverse image, and the generic localized-site theorem that restriction has an exact extension-by-zero left adjoint. I verified that these hypotheses apply to the open immersion b. The injective conclusion follows by the displayed Hom adjunction and exactness, with no extra hypothesis. Step 3 uses the existing K-injective-resolution existence theorem and exact inverse image; applying the degreewise Step 1 identity computes both derived functors. I checked edge cases a=id, U=empty, and L=0, where the isomorphism reduces respectively to identity, zero, and zero complexes. The Mathlib search log records LeanSearch as unavailable, LeanFinder with only unrelated open-subscheme declarations, Loogle as unavailable due an unknown identifier, and grep with no matching derived direct-image theorem.

## Second reading by NA

- Statement: checked against the blueprint node and its definitions of the cartesian square, schemes, and derived categories; all hypotheses and the natural isomorphism agree, including the empty-open and zero-complex cases.
- Step 1: checked against Stacks tags 03S2 and the existing direct-image and etale inverse-image-restriction node statements; the fibre-product section calculation is exactly what the cited statements provide and is natural in the sheaf.
- Step 2: checked against Stacks tags 03S2/03F3 and the existing localization, exact inverse-image, extension-by-zero, and site-restriction statements; the Hom adjunction plus exactness proves preservation of injectives under precisely the stated hypotheses.
- Step 3: checked against Stacks tags 05TI/05TH and the existing K-injective-resolution and exact-inverse-image statements; degreewise Step 1 identifies the complexes and hence the derived functors, with restriction compatibility explicit.
- New nodes: none; therefore B1--B7 and duplicate/Mathlib-node checks are vacuous. Existing-node searches were made by tag and keyword across `dag/nodes`.
- Changes: none to the worker's node or citations; this second reading only added this audit section. Dry-run delivery passed preflight.
