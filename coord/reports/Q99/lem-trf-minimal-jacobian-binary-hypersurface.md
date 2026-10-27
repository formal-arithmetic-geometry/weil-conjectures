# Stage-1 report: lem-trf-minimal-jacobian-binary-hypersurface

## Files written

- dag/nodes/sec-trace-formula/lem-trf-minimal-jacobian-binary-hypersurface.json: item, statement, split. No Mathlib match after two semantic phrasings and the recorded Loogle and grep searches.
- citations.json: ten verbatim citation entries, one for every use in the six proof steps.
- report.md: this report. searches.jsonl is the unmodified search-command log.

No new nodes; zero new Mathlib leaves. The existing statement and statement dependencies are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the exact item id and for minimal Jacobian, binary hypersurface, quadratic polar and Jacobian-depth phrases, including the RingTheory and AlgebraicGeometry directories. No project declaration states this item. The Mathlib formal derivative is already represented by def-trf-formal-power-series-partial-derivative; it does not prove the item.

## Wanted literature

None. Read the local Stacks source curves.tex: Tag 0C4C, lemma-fitting-ideal, in full; Tag 0C48, lemma-reduced-quotient-regular-ring-dim-2, statement and proof; and the neighboring paragraph defining nondegeneracy by the polar matrix. Read algebra.tex Tag 032C, remark-Noetherian-complete-local-ring-universally-catenary. Tags were checked in literature/stacks-project/tags/tags.

## Audit findings and corrections

The item is mathematically correct, including characteristic 2 and the conventions for e=0,1 and too few columns. There is no STATEMENT-DISPUTED correction. Its original proof was empty. I supplied the minor-order contradiction, the explicit generator-change calculation, and the final cotangent determinant argument, reusing the existing depth-one surface theorem and power-series regularity theorem rather than making copies.

Read the chapter and unit records, the three levels of SETUP.md, GOAL.md, the worker role, stage-1 contract, tools README, and both copies of delivery-errors.md B through E. Read the current latest blueprint (main-20261023-1620) locality statement and proof and sk-i-curve-zero section. The algebra item is an auxiliary node on the existing nodal-geometry dependency chain, not the unit's key statement; no chapter or unit file is modified. The current locality text has no equivalent algebra statement. Whole-blueprint searches for hypersurface, Jacobian and quadratic found no equivalent imported node, so blueprint.same_as remains []. Its inherited blueprint.from identifies the nodal ingredient below locality and is retained.

The cross-unit power-series theorem is declared in split_report.tool_uses as a generic algebra tool, used only for locality and regularity. This does not replace a unit proof step. All other non-elementary inputs are already in the same unit. A transitive dependency read found no path from these cited inputs back to the item.

## Not duplicates

No new nodes were created. The DAG search for 0C48 located lem-trf-regular-surface-depth-one-principal, which is used directly. The search for regular power-series rings located lem-weil-pbc-power-series-field-cohen-regular-complete, whose field case suffices. The existing Jacobian-minor-invariance node is unnecessary: for this one-column specialization, Leibniz and two finite generating expressions prove the equality directly in step 4.

## Mathlib searches

The six searches performed in this sandbox are recorded exactly in searches.jsonl and appended to the item's inherited searches. All services answered. LeanFinder with two phrasings returned standard smooth polynomial presentations and univariate Weierstrass preparation, rather than a theorem about depth-one minimal formal quotients. LeanSearch likewise returned Weierstrass division. Loogle's MvPowerSeries/Ideal.depth query had zero hits; MvPowerSeries.pderiv returned the formal derivative and its coefficient and Leibniz formulas. The grep for Jacobian/depth or quadratic hypersurfaces had zero hits. I read the derivative source, StandardSmooth.lean:54-63, WeierstrassPreparation.lean:160-185 and Presentation/Core.lean:248-270 to distinguish those candidates from the item. None is an exact match or a one-line specialization.

## Review by Q99

I checked each argument against the sources and the actual statements of every cited node. The source route is the minimal (t=0) case of 0C4C, not the full coordinate elimination, which the parent handles separately. Both non-elementary inputs are established as standalone DAG statements and neither needs reducedness or a characteristic assumption here.

Step 1 uses the field case of lem-weil-pbc-power-series-field-cohen-regular-complete, whose first two clauses explicitly give the local ring, variable maximal ideal and residue field. The quotient argument is written out and proves that m is proper; thus D=R for e<=1 contradicts D=m without any convention about negative minors. This also checks the e=0 field case.

Step 2 uses the coefficient formula in def-trf-formal-power-series-partial-derivative to put every derivative in p, the permutation-product formula of def-weil-pbc-matrix-determinant to put each positive-size minor in p^(e-1), and the actual Cauchy product in def-weil-pbc-multivariate-power-series to rule out z_1 in p^2. The inverse image of the minor ideal is the ideal of the lifted minors plus H; H is contained in p^2. Thus e>=3 is impossible, also when the generator list is empty or too short. This is an elementary determinant calculation, not an uncited order theorem or Nakayama invocation.

Step 3 again uses the power-series theorem, this time its fourth clause with d=2. Its statement says exactly regular local of dimension two. The statement of lem-trf-regular-surface-depth-one-principal requires only H inside the maximal ideal and depth(S/H)=1; both are given. It supplies a nonzero principal generator, and membership in H strengthens its order to at least two. I read 0C48(2)'s proof as well as this node's statement; the proof never uses the reduced alternative of 0C48(1).

Step 4 uses precisely the Leibniz rule in the derivative definition. The two generating expressions h_j=a_j f and f=sum b_j h_j exist because both generate H. The unwanted terms vanish modulo H. This proves both ideal inclusions and does not assume a unit coefficient or irredundant original list. No general change-of-generators lemma is hidden here.

Step 5 uses the same coefficient formula and the power-series definition to compute the two linear parts and identify p/p^2 with the linear coefficients. Because H is contained in p^2, it makes no linear relations. In two variables the remainder after the linear part groups into u^2 A+uv B+v^2 C, so it lies in p^2; uniqueness follows by reading coefficients. Thus the cotangent identification does not invoke a comparison theorem.

Step 6 reduces the given generating expressions for u and v modulo m^2, so coefficients become elements of F and the two derivative vectors span F^2. The elementary two-vector determinant argument is written explicitly, and the determinant definition gives 4ac-b^2. No characteristic restriction entered any step. At characteristic 2 this is -b^2, so b must be nonzero. Checked examples: f=uv works in every characteristic; f=u^2+v^2 fails the gradient hypothesis in characteristic 2; f=u^3+v^3 cannot have D=m; H=0 has zero derivative ideal for e>=2. These checks distinguish the assumptions from stronger reducedness or nonzero-quadratic hypotheses that were not assumed.

I checked B1-B10: no new statement-only nodes to validate or duplicate, all notions in the item retain their definition dependencies, TeX and citations are literal, all newly recorded searches were actually run, and blueprint provenance is filled. For C1-C8, the only substantive black boxes are the two cited theorems with the exact conclusions above; elementary coefficient computations are written out, quotations were verified against the full statement strings, dependencies equal the union of uses, and off-unit tool use is declared. D1-D5: the item itself carries its dimension and discriminant arguments rather than restating its clauses as new nodes. E1-E7: every applied theorem's hypotheses, the zero/small dimensions, redundant generators, and characteristic 2 were checked. No step exceeds 2000 characters.

## Unfinished work

None in the mathematical split. Stage 1 only: no Lean was written, compiled or built.
