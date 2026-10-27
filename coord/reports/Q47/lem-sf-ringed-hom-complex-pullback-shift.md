# Stage-1 report: lem-sf-ringed-hom-complex-pullback-shift

## Files written

- `dag/nodes/sec-six-functors/lem-sf-ringed-hom-complex-pullback-shift.json`: existing statement, now split into six steps; no Mathlib match.
- `citations.json`: one verbatim statement quote for each step/node citation.
- `searches.jsonl`: actual Q47 searches produced by msearch.py.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. The sandbox initially had only dispatcher marker files; there was no prior split or report to recover. The item was copied from the live read repository. Its statement, original source, original searches, blueprint ancestry and other metadata are retained.

## Attachments

None. Searching the full project source for the item tag and related notions found no declaration giving all clauses for an arbitrary exact ringed-topos module pullback. `CategoryTheory.homComplex_shift_left` in `WeilConjectures/Algebra/Homology/HomComplexShiftLeft.lean` proves a source-shift natural isomorphism, but does not give the pullback map or its square. `AlgebraicGeometry.SheafPullbackResolution.homPullbackMap` in `ExtPullbackHomComplex.lean` maps global morphism cochains, with a single source object, rather than the internal sheaf Hom complex. Neither is an attachment for this item.

## WANTED

None. All sources used are in the read repository.

## Problems found and changes

The statement is correct and unchanged. The imported item had no proof. I supplied evaluation transposition, the differential identity, two-variable naturality, the signed shift and its inverse, the sign verification, and the explicit evaluation identity proving the comparison square.

Stacks sites-modules.tex Tag 0GMX, `remark-pullback-internal-hom`, constructs the ordinary pullback/internal-Hom map for ringed sites. I read it as motivation, not as a theorem already proving this item's assertion for arbitrary ringed topoi and unbounded Hom complexes. Tag 03EL, `lemma-tensor-product-pullback`, is stated for ringed topoi and supplies the needed tensor comparison. Tag 03EO, `lemma-internal-hom-adjoint-tensor`, gives the natural closed adjunction. In sites-cohomology.tex I read Tag 0A8X, `section-hom-complexes`, for the product definition and differential; Tag 08JC, `lemma-RHom-triangulated`, only asserts triangulatedness and omits details. The chain and sign computations here are therefore marked agent-written, not falsely attributed to a ready-made Stacks theorem.

The nearest blueprint ancestor is `lem-weil-finite-duality-site-comparison`. I read its current main-20261015 proof at `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/lem-weil-finite-duality-site-comparison.proof.md`. Its second paragraph asserts that the Hom comparisons form morphisms of triangles. This item supplies the signed ordinary-complex calculation needed by that assertion through `lem-sf-site-hom-comparison-thick`; it does not change the ancestor's route or the unit or chapter records. No prohibited SGA source was used.

## Searches and reuse

Q47 ran msearch.py with two LeanFinder phrasings, LeanSearch, two Loogle queries and source grep searches; their exact queries are appended to the item's inherited search records. The original Q55 searches remain as inherited history, without claiming Q47 ran them. All Q47 services answered. The initial grep against `Algebra/Homology/HomComplex.lean` used the wrong Mathlib path and yielded no hits; after Loogle supplied the actual module I ran a corrected search against `Algebra/Homology/HomotopyCategory/HomComplex.lean` and read lines 904–950. Its `Cochain.map`, `map_v` and `δ_map` concern global morphism cochains in an additive category, not sheaf-valued internal Hom. I also read `CategoryTheory/Monoidal/Closed/Basic.lean` lines 292–310 and the ordinary pullback declarations in `PullbackContinuous.lean` and `PullbackFree.lean`; none supplies the item by a one-line specialization. The shift-functor hits only identify termwise functors with shifts, and do not provide the evaluation comparison square.

Whole-blueprint searches for Hom complexes, internal Hom complexes, source-shift and 0GMX, and DAG searches for the tag and shift/pullback notions found no blueprint node stating this general assertion. No nodes were created: products, Hom functoriality and the differential are already stated in `def-pur-hom-complex`; the two non-elementary tensor/closed tools are existing nodes; the remaining signs and indices are explicit calculations.

## Not duplicates

No new nodes. The existing `lem-sf-etale-hom-complex-pullback` is the special case of constant coefficients and the small-etale pullback along a scheme map. It does not imply this assertion for arbitrary ringed topoi. The existing `lem-pur-hom-complex-shift-left` states existence of a natural isomorphism but does not specify the component formula or compare pullbacks, so I did not extract the signed formula from its proof as though it were part of its statement. Likewise `lem-pur-inverse-image-hom-comparison` assumes a scheme isomorphism and is not usable for the arbitrary morphism here.

## Review by Q47

I checked delivery-errors B–E against the six written steps, their cited statements and the source passages above. There are no statement-only children concealing a proof, elementary children, restated clauses, or new Mathlib leaves to audit. I kept the original statement and its seven statement dependencies. Every mathematical object in the calculation has the site's module category and the indicated degree. The smallness and commutativity hypotheses are exactly those needed by the existing tensor comparison and closed module category.

For step 1 I opened `def-pur-hom-complex`, which explicitly gives the sectionwise product, `def-pur-sheaf-hom`, which supplies the linear sheaf maps, `lem-pc-sheaf-modules-tensor-closed`, which states symmetry, additivity and the natural adjunction, and `lem-weil-pbc-ringed-topoi-module-pullback-tensor`, which states the tensor isomorphism natural in both modules. Thus the product and transposition construction uses the statements of those nodes. Exact module pullback is additive; its effect on signs is the additive functor axiom. Additivity of transposition is also explained by evaluating sums.

For step 2 I checked the displayed evaluated differential directly against `def-pur-hom-complex`. Both terms have domain H^n tensor E^p and target I^(p+n+1). The same two existing tool statements justify applying tensor naturality and transposition. Product extensionality finishes the chain identity. For step 3 the same Hom-complex statement explicitly gives contravariant and covariant functoriality by componentwise composition. Its evaluation identity has the correct arrows u:E' to E and v:I to I'. After applying F, both candidate maps uncurry to the displayed composite. No assumption of an isomorphism of Hom sheaves is used.

For step 4 I checked the p-m and r+m indices and inverse signs using the Hom product formula. `def-weil-abstract-derived-category` supplies the cohomological shift convention in degree one; the statement itself explicitly specifies the general integer convention. This citation is not used to assert a hidden arbitrary-shift comparison theorem. Step 5 writes both coefficients of the chain identity: the postcomposition coefficient is (-1)^(mn+m), and the precomposition coefficient is -(-1)^(mn+n). These follow directly from that convention and the cited Hom differential on either site.

For step 6 I verified both uncurried maps have domain F(H(E[m],I)^n) tensor FE^p and codomain FI^(p+n-m). Tensor comparison naturality applies to sigma=s^n and the identity of E^p. Its statement supplies exactly that naturality; the closed adjunction supplies injectivity of transposition. Applying F to the displayed evaluation identity gives the same sign and composite on both sides, proving the square as chain maps. These two tools are declared in `split_report.tool_uses` as generic tools of other units, rather than silently changing the unit route.

I tested m=0 (identity reindexing), m=1 and m=-1 with n even and odd (both differential signs), the zero source and zero target, and characteristic two (all negative signs become positive). All index and parity identities work for negative integers too. With E and I both the complex having Z in every degree and zero differentials, and F=Q tensor_Z - on the point topos, c in degree zero is the usual map from Q tensor (product Z) to product Q. A family with unbounded prime denominators need not be in its image. The proof is still valid: it constructs a map into the product and never assumes the comparison is invertible or that F preserves infinite products. No boundedness, flatness or injectivity enters any step.

Every step is below 2000 characters. I checked that none hides a separate non-elementary lemma: evaluation transposition and tensor naturality are the cited existing tools; the remaining arguments are written component identities, product universal properties, and integer signs. The citations file quotes the full Hom-complex statement where several clauses are used, and verbatim relevant parts of the other statements. I did not cite an existing proof's internal construction as though it were its statement.

## Unfinished

None in this one-level stage-1 split. No Lean was written and no compiler or build tool was run. The required remote dry run and delivery follow this review.
