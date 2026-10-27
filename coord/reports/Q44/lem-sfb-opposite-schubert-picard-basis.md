## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-opposite-schubert-picard-basis.json: item, split into seven steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-schubert-closure-cell-geometry.json: new statement-only geometric input; not in Mathlib. It states Bruhat subword closure order and cell dimensions/tangent spaces, with no Picard conclusion or divisor-degree assertion.
- citations.json: a verbatim statement quotation for every step/node pair.

## Attachments

None. I searched lean/WeilConjectures for the item tag, Schubert, Bruhat, opposite Schubert and Picard basis. No declaration there supplies this statement; the Picard tensor-basis declarations found concern constant sections of curve modules, not flag varieties.

## WANTED

WANTED: Brion–Kumar, Frobenius Splitting Methods in Geometry and Representation Theory, Section 2.1 pp.61–63 and Exercise 2.2.E(2) pp.70–71, for lem-sfb-opposite-schubert-picard-basis and lem-sfb-schubert-closure-cell-geometry. The repository's named PDF is absent. I read the primary author-hosted PDF at https://www-fourier.univ-grenoble-alpes.fr/~mbrion/fbook.pdf, PDF pages 70–72 and 79–80 (printed 61–63 and 70–71), rather than claiming a local document exists. The assembly proof is marked agent-written, as the brief prescribes when the document is missing locally.

## Corrections and route

The imported statement is mathematically correct; no hypothesis or conclusion changed. Its doubled TeX backslashes were normalized to single TeX escapes. The all-characteristic heading for the exercise matters: no Frobenius-splitting argument, characteristic-zero reduction, or SGA result is used here.

I read the chapter and unit records, SETUP's three levels, and the latest blueprint's det-thm-sf-ctf-stability-direct-images proof. This item is a supporting algebraic-group input far below that unit's direct-image step, through the inherited fundamental flag-boundary chain. The ancestor command returns None, agreeing with the live item's null blueprint.from.node; the inherited specific place/via are retained and extended on the new node, without inventing a blueprint identity. Searches of the whole imported blueprint for Schubert, Bruhat, closure cell and tangent root found no equivalent node; divisor degree found the unrelated Picard-main unit. The latest blueprint contains no Schubert-specific replacement.

The seven proof steps carry the boundary, degree and Picard arguments. The new geometric lemma is not a renamed clause of the item: it deals with every Weyl element and its cells and never mentions Picard groups, Cartier divisors, degrees or a basis. Its non-elementary content is the subword/closure theorem and the scheme-theoretic orbit tangent description. Its later worker will split that theorem; no proof or proof dependencies are put into its unsplit node.

## Not duplicates

lem-sfb-schubert-closure-cell-geometry vs lem-sfb-bruhat-longest-cell-charts: the existing statement gives Bruhat strata and affine charts, the longest cell and integral flag scheme, but no closure order, length grading, or the tangent spaces of all ordinary and opposite cells.

lem-sfb-schubert-closure-cell-geometry vs lem-sfb-flag-torus-fixed-geometry: the existing statement gives fixed points and the ambient tangent weights; it does not identify the tangent subspaces to the two cell families or their closures.

lem-sfb-schubert-closure-cell-geometry vs lem-sfb-unipotent-root-intersection-products: the existing statement concerns intersections of Borel unipotent subgroups and root products, with no Bruhat closure or Schubert strata assertion.

lem-sfb-schubert-closure-cell-geometry vs lem-sfb-homogeneous-line-schubert-curve-degree: the existing statement gives rank-one projective lines and associated-character line degrees; it has neither closure incidence nor general cell tangent spaces.

lem-sfb-schubert-closure-cell-geometry vs lem-sfb-opposite-schubert-picard-basis: the new statement is geometric input, not the Picard classification or any of its asserted divisor intersection degrees. All those consequences are proved in the item.

lem-sfb-schubert-closure-cell-geometry vs lem-sfb-flag-effective-picard-generators: the existing statement only gives the existence of some effective generators for the flag Picard group, not Schubert closure geometry or their identification. It is not used as if it identified these particular divisors.

Before writing the new node I searched the entire DAG by Schubert, Bruhat, flag variety and Picard/boundary concepts, read the above candidate statements and the existing regular divisor dictionary and affine-space Picard results, and searched the project Lean source. No existing exact or more general node gives the new input. The new source contains no Stacks tag, so there is no unreported same-tag pair. Existing Stacks inputs are reused, not duplicated.

## Review by Q44

I read Brion–Kumar Section 2.1, including the subword description, the dimensions of both cell families and the opposite-cell paragraph, then Exercise 2.2.E(2) with its arbitrary-characteristic heading. I also read Milne iAG2017 printed pp.446–449 (Theorem 21.73 and the root products of Proposition 21.77), and Remark 22.49 on printed p.480. The latter is corroboration only, not an unproved Picard black box. For the new node the cell tangent formulas are the images of the positive and negative root spaces in the quotient by Ad(n_w)Lie(B). They use torus characters rather than Lie differentials, so the argument does not lose weights in small characteristic. The source and all group hypotheses, representative choices, definitions of length/subword order and the reduced closure convention are explicit in that node.

For step 1 I opened each of its six cited nodes. The Borel-pair statement expressly says semisimple implies reductive; flag-torus geometry expressly gives smoothness and projectivity; the chart lemma gives integrality and a finite affine-space cover; the smooth-over-field regularity lemma gives regularity and local Noetherianity; the divisor dictionary applies to a regular Noetherian separated scheme; and the homogeneous-line Schubert-curve statement expressly provides the SL2/B isomorphisms. I checked that the last statement has no dominance restriction when used here. No partial Picard result is treated as an attachment.

For step 2 the new closure statement supplies both integrality/dimension and the opposite closure formula. The subword argument is written out: each nonempty word contains a simple reflection; equal length comparable elements are equal. This proves coverage and distinctness, rather than just calling the complement a boundary. I opened the UFD node: its conclusion gives unique factorization for a regular local ring, with the empty parameter family allowed. Its height-one prime calculation really yields a generator which is a nonzerodivisor, hence the given reduced subscheme is effective Cartier. I read Stacks divisors.tex lemma-weil-divisor-is-cartier-UFD (Tag 0AGA) to check this local calculation; this tag is carried by the cited divisor dictionary, and the local argument itself is written out rather than passed off as a separate new node.

Step 3 uses only the chart lemma's explicit involution assertion w0^2=1 and the definitions of the two cells. I checked the representative issue: n0 need not square to the identity; its square is in T, which suffices. The two equations for translated opens are written out. This avoids assuming connected group translations act trivially on Picard groups.

In step 4 the new closure statement excludes e1 and identifies which simple fixed point lies in E_i; the rank-one node's group homomorphism and first-column model give the displayed diagonal action. Its nonendpoint orbit is transitive geometrically even in characteristic two, since the square map on nonzero algebraically closed-field elements is surjective. This is a support argument only and makes no false separability assertion. A closed invariant intersection containing a nonendpoint would contain e1; this is the elementary reason the support calculation is complete.

Step 5 uses exactly the new node's smooth-open-cell and complementary-tangent assertions at e_sj. I checked smoothness is needed there only near that point, not on the whole Schubert divisor. The local equation has nonzero image in the curve's cotangent space, so Nakayama gives multiplicity one; no unspecified intersection-multiplicity theorem is invoked. Restriction of the fractional-ideal definition gives the asserted restricted divisor line. I opened lem-pc-degree-agrees-sc: it says precisely that an effective divisor's Euler degree is its divisor degree, and in particular a rational point has degree one. Thus this citation supplies the actual degree conclusion, unlike citing merely a definition of degree.

For step 6 I opened the affine-space invertible-trivial node and the full regular-space divisor dictionary, and read Stacks divisors.tex lemma-open-subscheme-UFD (Tag 0BDA). The former applies to the opposite open cell since it is a translate of the known affine N-space. The latter dictionary gives a rational section's finite Weil divisor and L isomorphic to its divisor line, including the generator criterion on an open. The support and local product calculations are explicitly the elementary argument that these particular E_i generate Pic(Q). We do not use the weaker existing node asserting unspecified effective generators.

For step 7 I opened def-sc-pic0, the Euler-degree definition, and the Riemann–Roch statement. The first explicitly defines a group homomorphism, whereas the second alone would not imply additivity. The Riemann–Roch line-bundle and structure-sheaf formulas identify their degrees for every line bundle, not just effective ones. The standard-vector calculation then gives both injectivity and surjectivity and an explicit inverse.

Small cases checked: G=1 gives N=r=0 and a point, so no nonexistent nonempty divisor is claimed; SL2 gives Q=P1, E1 the simple fixed point, and D1 the other endpoint outside the longest cell; a product of two rank-one groups gives two distinct boundary components and off-diagonal degree zero. For all ranks the point e1 is outside every opposite divisor, which is essential to the orbit argument. Characteristic two is handled with characters and geometric square roots, not differentiated weights or a separable square map. No simply-connected weight-lattice theorem, projectivity of a new quotient, invariant-section theorem or Picard vanishing of G is silently used.

All proof steps have fewer than 900 characters, so none triggers the 2000-character hidden-lemma review. Elementary steps contain the actual orbit, local-uniformizer, rational-section and inverse calculations. Every cited node statement has been read and is quoted verbatim in citations.json. Every new-node Mathlib search is copied from an actual msearch invocation, with exact tool/query and inspected results. Searches found only abstract root/Coxeter/Lie facts, topological bundles and ring Picard groups; grep found no flag geometry (the lone broad grep hit is a Bruhat–Tits-tree comment). Both semantic rephrasings and Loogle were tried, and no service was recorded as unavailable when it returned hits.

No mathematical statement dispute, route change or unresolved proof obligation remains in the item's split. The new geometric lemma is intentionally statement-only. Validation results will be recorded below after the required server dry run.

## Validation

Required deliver.py --no-push completed successfully: OK (not pushed), preflight passed, commit 80f8196db96. Citation and recorded-search checks passed, and the server's delivery preflight ran its DAG/split checks successfully. There is one new unsplit node and zero Mathlib leaves. No compiler, Lake, local DAG-check script, repository write or manual git command was used. The final authorized push uses the same delivery tool after that dry-run process exited.
