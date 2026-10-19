# Stage-1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/prop-weil-pbc-comparison-direct-image.json`: item split in place, no new nodes.
- `citations.json`: seven step-to-node quote entries.

## Attachments

None. The source declaration `AlgebraicGeometry.ProEtale.rightDerivedLowerStarComparisonPlusIso` (and its unbounded variant `rightDerivedLowerStarComparisonIso'`) is tagged with the blueprint id in `WeilConjectures/SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean`, but its body contains `sorry`; it therefore is not a finished attachment under the stage-1 rule.

## WANTED:

None.

## What was wrong or incomplete in the imported node

The imported proof had a real citation gap in its bounded-below sentence and in the continuity/evaluation paragraph. I added `prop-weil-pbc-inverse-image-exact` and `lem-kun-tensor-t-est` to step 2, and `lem-weil-pbc-derived-cohomology-continuity` and `lem-weil-pbc-etale-restriction-injectives` to step 4. The proof dependency list now is exactly the union of the step uses. No statement or hypothesis was changed, and no new node was needed because all invoked facts already have nodes. The item itself is not a Mathlib theorem; the recorded searches found only generic étale-category declarations.

## Review by NH

I read the item’s blueprint proof at `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/prop-weil-pbc-comparison-direct-image.md`, the chapter and unit records, and the source declaration/docstring in `WeilConjectures/SixFunctors/ProEtale/BaseChange/SmoothBaseChange.lean`. The source declaration has a `sorry`, so I retained the natural-language split. The statement retains exactly quasi-compactness, quasi-separatedness, bounded-below derived étale coefficients, the comparison isomorphism, and identity/composite/naturality compatibility.

Step 1 cites `lem-weil-pbc-comparison-pullback`, whose statement supplies the natural pullback isomorphism used to form the pulled-back counit. Step 2 cites `prop-weil-pbc-inverse-image-exact` for exact inverse images and `lem-kun-tensor-t-est` for preservation of lower bounds by derived direct image; these are exactly the two non-elementary boundedness assertions. Step 3 cites `lem-weil-pbc-comparison-global-cohomology` for the étale/pro-étale derived-sections comparison and uses only the stated qcqs and affine-transition hypotheses for the basis system. Step 4 cites `lem-weil-pbc-derived-cohomology-continuity` for both inverse-limit continuity applications and `lem-weil-pbc-etale-restriction-injectives` for restriction of injective resolutions; its middle evaluation is therefore supported by a node rather than an uncited slogan. Step 5 cites `lem-weil-pbc-comparison-global-cohomology` and `lem-weil-pbc-proetale-restriction-injectives`, matching the two displayed pro-étale identifications and the injective-resolution argument. Step 6 cites `lem-weil-pbc-comparison-injective-acyclicity` and `lem-weil-pbc-comparison-sections`, which state respectively basis acyclicity and the filtered-colimit section formula used to identify the actual mate. Step 7 cites `lem-weil-pbc-basis-derived-detection` for detection on every affine ind-étale basis object; identity, composition, and naturality follow from the counit and the pullback node’s coherence clause.

I opened every cited node and copied its statement verbatim into `citations.json`; there are no citations to proof internals. I checked edge cases in the natural-language statement (identity morphism and an identity composite reduce to the counit/triangle identities, and the argument never assumes a nonempty basis beyond the stated basis-object quantification). The Mathlib searches were run for the item with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such, while the other searches found no matching theorem. No new node was created, so no new-node search or duplicate pair was required.

## What could not be finished

Nothing beyond the intentionally unsolved source declaration; stage 1 forbids writing Lean or compiling it.

## Second reading by NH

- Item statement: checked against the imported blueprint node, the comparison convention (fixed finite discrete coefficient ring), and Stacks proetale.tex, label lemma-morphism-comparison (Tag 09A6), within section-comparison (Tag 099R). The source gives qcqs direct-image comparison for sheaves; the bounded-below extension is the injective-complex argument in steps 2 and 6. No hypothesis or conclusion changed. Zero complexes, the empty scheme, the identity of a field, and degrees 0 and 1 cause no exceptional case.
- Step 1: opened lem-weil-pbc-comparison-pullback and the direct-image/operations definitions; the coherent inverse-image identification supplies exactly the pulled-back counit. PASS.
- Step 2: the original lem-kun-tensor-t-est only states an étale abelian-sheaf result, and prop-weil-pbc-inverse-image-exact only covers étale inverse images. Replaced them by site-pullback exactness, general injective representatives and general right-derived computation. Opened lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives: their statements apply to the small ringed sites in the fixed larger universe. Module exactness follows from underlying kernels/cokernels; applying an additive functor termwise leaves zero degrees zero. FIX.
- Step 3: opened the global comparison, pullback comparison, both restriction-of-injectives nodes, ind-etale-basis and quasi-compact-base-change. They supply derived local evaluation, the covering basis and qc base change; the relative and absolute diagonal argument verifies qs. Local vanishing follows by the sheaf axiom on cohomology sheaves of the cone. These are the hypotheses used in Stacks lemma-morphism-comparison's affine-local proof. FIX.
- Step 4: opened derived-cohomology-continuity and etale-restriction-injectives. Both limits have qcqs stages and affine transitions; moving to the cofinal overcategory of a fixed stage ensures the coefficient complex descends from that stage, as the continuity statement requires. Evaluation of the injective section complexes gives the middle equality. Wrote the exact-left-adjoint/injective-right-adjoint argument. FIX.
- Step 5: opened global-cohomology comparison, proetale-restriction-injectives, ind-etale-stability, pullback comparison and site-pullback exactness. The ind-etale map and its base change are weakly etale, which checks the actual hypothesis of the restriction lemma for both evaluation sites. FIX.
- Step 6: opened comparison-injective-acyclicity and comparison-sections, and read proetale.tex labels lemma-affine-vanishing (099U), lemma-limit-pullback and lemma-describe-pullback-from-etale. Opened leray-acyclicity-quasi-iso and general injective representatives: evaluation preserves the resolution quasi-isomorphism since both bounded-below complexes have acyclic terms. The sections formula is degreewise, and the counit sends a finite-stage section to its restriction on the fibre product, so the resulting colimit map is the named mate. Added the missing acyclic-complex citation. FIX.
- Step 7: opened basis-derived-detection and comparison-pullback. Detection applies to bounded-below objects on affine V; step 3 then recovers the global assertion. The counit of a composite is the composite of the two counits; the coherent pullback comparison and triangle identities give the stated composition law and identity law. Added the coherence citation actually used. FIX.
- New nodes: none; therefore B1–B7, duplicate checks and new-node Mathlib-leaf searches have no new object to check. All added references are existing DAG nodes, found by id and statement-keyword searches; no existing-node proof internals are used. There are zero new Mathlib leaves.

Changes: repaired the site/coefficient mismatch in the boundedness citation; added explicit local, diagonal, weakly-etale and fixed-stage hypotheses; cited the bounded-below acyclic-complex evaluation theorem; regenerated every step citation verbatim; replaced the vague external section reference with exact Stacks tag/label pairs. The source proof's finite coefficient convention is made explicit in step 2 without changing the imported statement.

Correction to the first reader's source audit: the current slopmaster2 rightDerivedLowerStarComparisonPlusIso has no direct sorry in its body. It uses rightAcyclic_lowerStar_comparisonUpperStar_obj_of_injective, whose acyclicity proof uses the sorry-backed rightAcyclic_comparisonUpperStar_obj_of_injective in Comparison/LowerStarAcyclic.lean (line 110). Thus the source still does not certify a finished proof, and the split remains necessary. No compiler or build was run; the upstream master archive and both source trees were read only.

Generic tools: lem-weil-pbc-ring-sheaves-grothendieck is in this unit and supplies the general ringed-site categorical input; lem-sp-grothendieck-enough-injectives supplies the categorical existence theorem, and lem-pc-quasi-compact-base-change the general geometric base-change input. No replacement of the proper-base-change unit route is involved. These proposed tool uses are reported here for the maintainer; no tool_uses field is installed by this reader.

Dry-run repair: the first attempt rejected the ringed-site tool in sk-def-sf-operations. Found the existing lem-weil-pbc-ring-sheaves-grothendieck, whose statement covers arbitrary small ringed sites and noncommutative rings, on the proper-base-change route; substituted it and regenerated the quotes. No tool rule was bypassed.
