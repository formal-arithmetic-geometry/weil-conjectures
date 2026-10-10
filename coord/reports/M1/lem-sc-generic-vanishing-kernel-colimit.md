1. Files written

- `dag/nodes/sec-curve-estimates/lem-sc-generic-vanishing-kernel-colimit.json`: item, statement node, split; no new nodes.
- `citations.json`: verbatim citations for all proof-step dependencies.

2. Attachments

None.

3. WANTED

None.

4. Problems found

The imported item was unsplit and had no proof. The Lean source constructs the same reverse-inclusion diagram over `NonemptyAffineOpensᵒᵖ` and proves monicity plus local surjectivity before the final isomorphism. I made the reverse-inclusion order and the transition direction explicit. No statement was changed.

5. Incomplete work

None.

## Review by M1

I read the item statement and its source context in `WeilConjectures/AlgebraicGeometry/Curve/GenericComparison.lean`, lines 164-211, together with the blueprint sentence in `lem-sc-generic-cohomology-comparison`. The source uses kernels of the affine-open adjunction units, a diagram over the opposite of nonempty affine opens, a canonical map to `G`, and the two properties mono and locally surjective. The item statement matches those objects and the generic-vanishing hypothesis.

For step 1 I checked `def-pc-integral-scheme` for nonemptiness and irreducibility, `lem-weil-pbc-affine-opens-basis` for affine refinements of the intersection, the inverse/direct-image definitions for the adjunction units, and `def-pur-abelian-sheaf-kernel` for the kernel and its canonical inclusion. These statements support filteredness, unit naturality, and the kernel transition maps. For step 2 I read the exactness statement of `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` and the universal-property statement of `def-weil-pbc-category-colimit`; together they say that filtered colimits preserve the short exact sequences and identify the constant colimit with `G`, yielding monicity. For step 3 I checked the sectionwise kernel statement and the full locally-surjective/epimorphism statement of `lem-weil-pbc-abelian-sheaf-epi-locally-surjective`; the hypothesis supplies exactly the required local kernel lifts. Step 4 uses the abelian-category assertion in `def-weil-pbc-abelian-etale-sheaves`, so mono plus epi is an isomorphism.

I searched the DAG for each cited fact before writing. The two general facts from the proper-base-change unit are declared in `split_report.tool_uses`, since this curve unit has no more specific replacement. I tested the edge case `U=C`, where `K_C=0` and the hypothesis forces the corresponding section to vanish, and checked that the reverse-inclusion direction gives `K_U \subseteq K_V` for `V\subseteq U`. Every citation quote in `citations.json` is copied verbatim from its node statement.
