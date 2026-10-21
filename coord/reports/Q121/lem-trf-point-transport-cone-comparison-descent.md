# Stage-1 delivery: lem-trf-point-transport-cone-comparison-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-point-transport-cone-comparison-descent.json`: statement, split in eight steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `searches.jsonl`: actual Q121 search records; the item's earlier Q91 searches remain in the node.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint tag and by point-transport and cone-comparison notions. The stalk transport in `TraceFormula/Slop/Stalk.lean` concerns geometric fixed-point stalks, not the specified ambient integral point-sections cone map. No completed project declaration states this item. No Lean was written and no compiler was run.

## Literature wanted

None. The proof is marked agent-written: the current blueprint clause (3) motivates the integral realization, but does not contain this entire explicit cone/roof calculation.

## Source error and statement clarification

STATEMENT-DISPUTED: the original statement allows arbitrary complexes N and explicitly disclaims derived completeness, but its reference `def-weil-derived-pullback-tensor-hom` introduces the integral operation only on the bounded constructible subcategory. That reference alone is insufficient to type Lg* N for general N. The existing `def-pur-integral-derived-operations`, already used by comparison (b), defines the ambient completed pullback on all D(s_proet, O_E). I changed the reference to that ambient construction and named its restriction to integral constructible objects. No hypothesis was added and no conclusion was removed. This is a reference/domain repair, not a new pullback construction.

The coefficient field E is not changed. The fixed point is over the algebraic closure k, so exact point sections apply. All C_n are restricted to the completed coefficient sheaf before taking products. Source sections and target sections in the displayed equations are complexes of O_E-modules via constant coefficients.

## Searches and existing nodes

Read the ancestor output and searched the whole imported blueprint for `cone comparison`, `point transport`, and `roof`. The four blueprint matches for point transport concern trace/coefficient comparisons and punctual weights, not this strict cone identification. DAG searches for resolving-class localization, K-flat roofs, and natural transformation descent found `lem-weil-pbc-site-derived-tensor-descent` and `lem-weil-pbc-localization-universal-property`; these are reused. I also read the existing operation-invariance and point-sections statements. No auxiliary statement is introduced.

Ran msearch leanfinder in two formulations, loogle for `CochainComplex.mappingCocone.lift`, leansearch, and source grep. All services answered. The cone constructor is generic; the derived exact-functor and ordinary pullback-comparison hits do not specify this pro-etale integral transport. Read `MappingCocone.lean` lines 282-307, including the zero-homotopy component formulas. The original searches have been retained, not claimed as searches run by Q121.

## Not duplicates

No new nodes. The coordinate calculations are elementary proof steps; the non-elementary localization, exactness, and invariance facts cite existing nodes.

## Review by Q121

I read the chapter and unit records, GOAL.md, the current blueprint `prop-trf-rational-frobenius-integral-model.proof.md` clause (3), and the whole statements of every cited node. The proof realizes the parent's integral-limit comparison route. It does not cite SGA or substitute another purity route. For the generic descent input I read Stacks sites-cohomology.tex, Tag 06YS (lemma-K-flat-resolution), Tag 0G7D (lemma-factor-through-K-flat, including its final flat-terms clause), and Tag 06YU (definition-derived-tor and the preceding construction). For natural-transformation localization I read Mathlib `CategoryTheory/Localization/Predicate.lean` lines 278-338, which backs the existing Mathlib leaf. These facts are cited through their actual DAG statements, rather than extracted from a node's proof.

Step 1 uses comparison (b)'s explicitly stated transition compatibility and chain-map properties. The reductions take x tensor 1 to x tensor 1 under the next quotient. Substitution into the actual displayed differential proves that both zero-first-coordinate maps are chain maps. Step 2 uses exactly the sectionwise product assertion of `lem-weil-proetale-countable-products-exact` and exact additive sections of `lem-weil-point-proetale-sections-exact`; the strictness equation explicitly shows that the same diagonal map acts on the shifted product. Step 3 evaluates the two maps and applies the hypothesis on u_n. In particular, it checks the full cone map, not only its finite projections.

Step 4 uses only clause (1) of `lem-weil-frobenius-point-transport-natural`, which expressly applies to arbitrary complexes, and exact sections to invert Gamma(q). I read the transported module inverse-image exactness assertion in the comparison definition: it specifically extends to the completed coefficient sheaf. The proof does not use clause (2), which would presume naturality of iota. Step 5 uses the ambient definition and the representative comparisons in `lem-pur-integral-operations-well-defined` (2). Comparison (b) specifies kappa as the displayed lift followed by the inverse resolution map. Cancelling Gamma(g^-1 q) after the sigma naturality equation proves precisely the asserted formula and allows cancellation of Gamma(q).

Step 6 checks naturality on tensor generators and on zero first coordinates. Its only extra hypothesis is exactly the item's conditional chain naturality of the u(P). Step 7 uses the existing site's universe convention, the resolving-class equivalence explicitly stated in `lem-weil-pbc-site-derived-tensor-descent`, and operation-invariance clauses (1),(2). The generic localization node explicitly supplies unique descent of natural transformations. Thus there is no assumption that one can choose strict chain lifts between arbitrary resolutions. Step 8 writes the algebra for both arrows of the roof and identifies the resulting component using step 5. Independence is supplied by unique descent with the specified representative comparisons, not by an assertion that an individual reduction determines a map.

I checked all dependencies for paths back to the item; none of the cited nodes leads to it. Off-unit statements are declared as generic tools in split_report.tool_uses. No proof step exceeds 2000 characters and none hides a new comparison lemma: the coordinate calculations are written, and the two non-elementary descent steps cite existing statements.

For edge cases, the zero complex gives zero maps on both products. For a flat localization P=N=R[1/varpi] concentrated in degree zero, every quotient P_n is zero and completed pullback is zero; the formula asserts a zero map from Gamma(P), not an isomorphism. This tests why no completeness assumption and no inverse to a_P can be used. Shifts retain the negative sign in the first coordinate, and strictness makes the first-coordinate obstruction vanish exactly, not merely up to homotopy. Roofs with a the identity reduce to chain naturality; a quasi-isomorphism is handled by inverting S(a) and T(a), whose invertibility is cited.

Against delivery-errors B-E: no statement-only auxiliary nodes or duplicate clauses were created; every non-elementary input has a node whose statement was read; citations.json copies the relevant text verbatim; the proof is marked agent-written and the domain-reference repair is explicit. The statement and all original blueprint/import/search metadata were retained except the stated reference repair. Nothing remains mathematically unfinished in this one-level split.

## Unfinished work

None for this split. Downstream existing nodes retain their own queue states. Server dry run and direct delivery are recorded by the delivery tool.
