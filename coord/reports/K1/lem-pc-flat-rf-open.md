1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-flat-rf-open.json`: statement split with no new nodes; Mathlib searches not applicable.
- `citations.json`: verbatim citations for every proof-step dependency.

2. Attachments: none. The slopmaster2 declaration `AlgebraicGeometry.Scheme.Modules.exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree` is Nat-indexed and rests transitively on sorry declarations, so it does not state this item exactly.

3. WANTED: none.

4. The imported proof already followed the blueprint route. I corrected its dependency accounting by adding the existing derived-direct-image and affine-cohomology statements to the local-complex step and to `proof_deps`. The bounded finite-free complex comes from the perfect-complex definition, its fibre pullback from the flat-complex pullback lemma, and the fibre cohomology identification from base change, higher-direct-image cohomology, and affine-base cohomology. The source and Lean formalization differ in index type (`\\mathbb Z` in the item versus `\\mathbb N` in the current theorem), so I did not claim an attachment.

5. I could not finish a formal Lean proof because this is a stage-1 natural-language split and the project contract forbids writing or compiling Lean here.

## Review by K1

I read the item source `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-perfect/lem-pc-flat-rf-open.md`, the corresponding unit text, and the tagged declarations in `WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage.lean`. Step 1 uses the derived-category definition, the perfect arbitrary-base-change statement, and the derived-pullback definition; each cited statement supplies exactly the construction it names. Step 2 uses the perfect-complex local bounded finite-projective model, the flat-complex pullback lemma, the arbitrary base-change statement, the derived-direct-image interface, affine-base cohomology, and upper semicontinuity; I checked each node's statement and recorded a verbatim quote in `citations.json`. Step 3 uses the perfect-locus characterization, whose statement gives the required factorization criterion for every integer degree and rank. I checked the hypotheses (proper finite presentation, finite presentation and base-flatness of the sheaf) against the item and found no missing hypothesis. I also checked the existing formal declaration and rejected attachment because its indices are naturals and its dependency closure contains sorry declarations.

## Second reading by K1

- Statement: checked against Stacks Tag 0B9S (`perfect.tex`, `lemma-open-where-cohomology-in-degree-i-rank-r-geometric`) and the blueprint node; hypotheses and the finite-locally-free rank-$r$ conclusion agree, including arbitrary integers $i,r$.
- Step 1: checked `def-pc-derived-category`, `lem-pc-rf-perfect-base-change`, and `def-pc-derived-pullback`; their statements provide $E$, perfectness, arbitrary base change, and the meaning of $Lg^*$ exactly as used.
- Step 2: checked the perfect-complex, flat-complex pullback, base-change, derived-direct-image, affine cohomology, and semicontinuity statements; the finite-projective-to-finite-free shrinking argument is now written explicitly, and negative degrees are handled separately because the affine cohomology node is stated for $q\ge0$.
- Step 3: checked `lem-pc-perfect-locus`; its factorization criterion applies to every $T\to S$, and the pointwise field calculation identifies its locus with the set $U$ constructed in Step 2.
- New nodes: none; the existing-node search covered every cited tag and the blueprint search found only the item itself, so no duplicate helper node was created. The existing slopmaster2 declarations were checked and not attached because their index types/dependency closures do not meet this item.
- Changes made: filled the item blueprint provenance (`from` and `same_as`), replaced the Step 2 “as in the proof” shortcut with the actual finite-projective localization argument, and stated the negative-degree convention needed for the all-integer quantifier.
