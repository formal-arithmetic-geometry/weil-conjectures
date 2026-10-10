# Stage 1 delivery: lem-pc-very-ample-ample

## Files written

- dag/nodes/sec-picard-framework/lem-pc-very-ample-ample.json: split into four sourced steps.
- dag/nodes/sec-picard-framework/lem-pc-ample-affine-loci-criterion.json: one new unsplit statement; no Mathlib match after LeanSearch, LeanFinder, and Mathlib source searches.

## Attachments

None. AlgebraicGeometry.IsVeryAmple.pullback_of_field in WeilConjectures/AlgebraicGeometry/Modules/Ample.lean:448 has sorry. AlgebraicGeometry.IsAmple.pullback_of_field at line 459 has no local sorry but calls that theorem, so it does not close the item.

## WANTED

None. I read the Stacks source at /home/ubuntu/c1-stacks-review/{properties,morphisms,schemes}.tex; the project's untracked literature/stacks-project/ is absent from this worker checkout, but these are copies of the cited Stacks files.

## Corrections

The imported proof inferred that the finitely many affine nonvanishing loci from the standard charts form a basis. A covering alone does not establish that. The new node uses the pointwise affine-locus definition of ampleness (01PS), then 01VT over the affine base to obtain a positive power with a projective immersion. Properness makes that immersion closed, and extending the defining sections to a basis gives the complete-system form required by def-sc-ample. The imported proof also left properness of X, affineness of the chart preimages, and compatibility of O(1) with field base change uncited; the split names those facts.

## Review by C1

I read Properties 01PS and 01Q3, Morphisms 01VK and 01VT, and Schemes 01IH and 01JY in the Stacks TeX copies. The item says that a closed projective embedding makes its pulled-back O(1) ample and keeps it ample after a field extension. Its hypotheses are enough: a closed subscheme of projective space over k is proper, and base change preserves a closed immersion. I checked the new criterion against 01PS and 01VT hypothesis by hypothesis: X proper gives quasi-compactness and finite type over k; the pointwise affine X_s condition is exactly 01PS; Spec(k) is affine for 01VT. The conclusion in 01VT is initially an immersion from a power, and the extra properness makes it closed. A basis of all global sections contains the finitely many defining sections; the complete-system map projects to the closed immersion on the open where those coordinates do not all vanish, so it is an immersion, and properness closes it.

Step 1 cites lem-pc-projective-proper for precisely the properness it states. Step 2 uses parts (a)-(c) of lem-weil-pbc-projective-space-standard-charts for the coordinate cover, the nonvanishing identity, and affineness of each projective chart; part (1) of lem-weil-pbc-closed-immersion-affine-cover-criterion says its preimage under a closed immersion is affine. Step 3 applies the exact hypothesis of the new criterion to the sections of step 2. Step 4 uses lem-pc-closed-imm-base-change for the closed immersion after extension, the chart node's definition of O(1) as a pullback from projective space over Z, and part (2) of lem-weil-pbc-invertible-pullback-tensor for the composition of module pullbacks; the same argument over K then proves the conclusion. The off-unit nodes supply generic projective and sheaf tools and are declared in split_report.tool_uses.

For the new node I searched the full DAG by its concepts and 01PS/01VT, searched the imported blueprint with tools/blueprint_refs.py, and checked the Lean source and Mathlib search record; no existing node or sorry-free Lean declaration states this exact proper-scheme criterion. It has a self-contained statement, names its notions, has no proof fields populated, and has its blueprint provenance. On the small cases X empty and X a point, the criterion gives the expected ample bundle; for X a finite disjoint union of points, each component has an affine X_s and a common positive power embeds the union. I corrected the draft's plain-text mathematical notation, missing properness/residue-field citations, and imprecise source: 01VT, with 01VK and 01PS, is the relevant implication. I also verified that the item has no dependency on itself or on a citer.

## Unfinished

The new criterion remains unsplit, as required for a new stage-1 node.
