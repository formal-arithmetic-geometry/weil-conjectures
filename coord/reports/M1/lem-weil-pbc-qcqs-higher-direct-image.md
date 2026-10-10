1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-qcqs-higher-direct-image.json`: the item, statement split into five proof steps; no new nodes were needed.

2. Attachments

- None. The two slopmaster2 declarations with this blueprint tag both contain `sorry` and are not exact matches to the abelian-sheaf wording: `AlgebraicGeometry.Etale.isIso_higherDirectImagePresheafToSheaf` and `AlgebraicGeometry.Etale.isIso_higherDirectImagePresheafToSheaf_singleFunctor`, `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage.lean:282-303`.

3. WANTED

- `WANTED: literature/stacks-project/derived.tex, Lemma 08BJ (13.31.9), for preservation of K-injective complexes by an exact-left-adjoint restriction.`
- `WANTED: literature/stacks-project/sites.tex, Lemma 00WJ (7.10.15), for exact sheafification and its commutation with complex cohomology.`

4. What was wrong or incomplete

- The imported proof hid the exact restriction/K-injective argument, the sectionwise identification, and the exact-sheafification argument in one paragraph. I expanded each into a separate step and added the missing statement dependency `def-weil-pbc-sheafification`.
- The imported `lean_audit.slopmaster2` said `none`, but the source checkout contains the two tagged declarations above with `sorry`; this mismatch is recorded here for the maintainer's audit refresh. Their module-coefficient statements are stronger/different in presentation, so I did not attach them.
- A whole-blueprint search found `sbc-lem-higher-direct-image-presheaf`, which states the same result in a stronger all-morphisms/complex form; it is recorded under `blueprint.same_as`. I did not cite it as a proof dependency because it belongs to another unit and is not needed for the route here.

5. What I could not finish

- No mathematical subnode remained to create. The Stacks source files listed under WANTED are absent from this checkout, so the proof origin remains the agent-written blueprint proof while the existing cited DAG statements supply the formal ingredients.

## Review by M1

I read the item record and its master-blueprint source reference (the referenced imported blueprint file is not present in this checkout), the `sk-thm-iff` unit record, and the tagged source declarations in `HigherDirectImage.lean`. I also read every cited DAG statement. There are no new nodes to review, so the new-node checks are vacuous.

Step 1 uses the statements of `def-weil-pbc-direct-image`, `def-weil-pbc-derived-categories`, and `def-weil-pbc-kinjective-resolutions`: together they introduce the bounded-below derived category, K-injective resolutions, and the computation `Ru_*K = u_*I`. The step does not assume an injective resolution beyond what the direct-image definition supplies.

Step 2 uses `lem-weil-pbc-etale-base-change-finite-limits` for the etaleness of `W x_V U -> U`, `lem-weil-pbc-etale-inverse-image-restriction` for restriction as precomposition, and `lem-weil-pbc-sheafification-exact` for sectionwise exactness. It uses `def-weil-pbc-etale-sum-extension` and the exact-left-adjoint assertion in `lem-weil-pbc-etale-restriction-injectives`; the closed node `lem-weil-pbc-right-adjoint-preserves-kinjective` then applies with restriction as the right adjoint to extension by zero. Thus the restricted complex is K-injective and remains a resolution. The quasi-compact and quasi-separated hypotheses are not used in this local calculation, as permitted by the stronger source result.

Step 3 uses `def-weil-pbc-etale-cohomology` to identify cohomology with sections of the restricted K-injective complex, and `prop-weil-pbc-cohomology-resolution-independent` to make that identification independent of the chosen resolution. The direct-image formula in `def-weil-pbc-direct-image` gives exactly the fibre-product sections and their restriction maps. The same argument applies to hypercohomology of a bounded-below complex.

Step 4 uses the Mathlib-leaf statements `lem-weil-pbc-sheafification-exact` and `lem-weil-pbc-exact-functor-complex-cohomology`, together with the definition `def-weil-pbc-sheafification`. Their hypotheses are an abelian presheaf/sheaf category and an exact sheafification functor; these are exactly the abelian etale-sheaf setting here. This yields the sheafification of the sectionwise cohomology presheaf.

Step 5 combines Steps 1, 3, and 4 separately for a sheaf in degree zero and for an arbitrary bounded-below complex. I checked the fibre-product orientation (`W x_V U` versus the base-change node's `U x_V W`) is related by the canonical symmetry isomorphism. I tested the edge cases `q = 0` and the zero sheaf: the sectionwise complex gives ordinary direct image in degree zero and the zero presheaf/sheaf in all degrees for the zero input. The old paragraph's hidden uses of Tags 08BJ and 00WJ are now represented by explicit cited nodes, and no new node duplicates an existing DAG statement.
