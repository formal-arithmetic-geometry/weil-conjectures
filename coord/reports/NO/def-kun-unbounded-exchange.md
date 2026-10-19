# Stage-1 worker report: def-kun-unbounded-exchange

## Files written

- `dag/nodes/sec-smooth-purity/def-kun-unbounded-exchange.json`: existing definition updated to `split`; no new nodes.
- `citations.json`: empty, because definitions have no proof steps.

## Attachments

None. The source declaration `AlgebraicGeometry.Etale.derivedBaseChangeMap` in `WeilConjectures/SixFunctors/BaseChange/DerivedUnbounded.lean:123` is a generic natural transformation for arbitrary commutative squares and abstract Grothendieck coefficient categories. It does not state this node exactly: the node is the Λ-specific cartesian-square definition, formulated as the component mate using the named K-injective extension. Therefore it is not an attachment.

## WANTED

None.

## What was wrong or incomplete

The imported node had `status: imported`, no split report, and no Mathlib searches. Its `uses_not_cited` entry for the cartesian-square definition is appropriate as a statement dependency, so I retained all three seeded dependencies. No statement correction was needed. The item is a definition, so there are no proof steps or proof dependencies to split into additional nodes.

## Review by NO

I read the item’s blueprint source at `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-unbounded-exchange.md`, the chapter and unit records, and the cited DAG nodes `def-weil-pbc-cartesian-square`, `def-weil-pbc-derived-exchange`, and `prop-weil-pbc-kinjective-resolutions-exist`. The item’s hypotheses and displayed mate composite agree with the blueprint. The cartesian-square node supplies the square and comparison θ; the derived-exchange node supplies the mate formulation and counit; the K-injective proposition supplies the unbounded extension. Since this node has no proof steps, there are no step citations to quote and `citations.json` is empty. I also inspected `DerivedUnbounded.lean`: its `derivedBaseChangeMap` is related but has broader abstract hypotheses and is not an exact declaration of this item. I ran LeanFinder, Loogle, grep, and LeanSearch searches; the first three returned only generic mate infrastructure or no matches, and LeanSearch was unavailable, recorded as such in the node. Small edge cases (identity square and zero complex) introduce no additional clause or dependency.

## Dependency audit correction

The first draft overstated what resolution existence supplies: that proposition gives resolutions, not an adjunction. I corrected the definition's description (without changing the morphism or hypotheses) to cite `lem-weil-pbc-kinjective-total-derived` for total right derivability, `lem-weil-pbc-exact-functor-derived-functor` for the exact left derived inverse image, and `lem-pc-derived-adjoint-functors` for their adjunction. I read these three statements in full. I also read `prop-weil-pbc-inverse-image-modules-exact`: its clause (3) supplies exactness and the sheaf module adjunction for every commutative coefficient ring, not just abelian sheaves. The module square comparison descends the termwise canonical comparison through clause (2) of the localization universal property; I cite that node rather than treating the abelian-sheaf-only square definition as a module theorem. The abelian square definition is used only for its explicit Z specialization. The mate node supplies exactly the explicit three-arrow composite. The statement now names the derived module categories and all these ingredients directly. These are statement dependencies of a definition, so the proof and citations list remain empty. No new lemma is introduced and no clause of the item is moved into a new node.

The smooth-base-change definition `sbc-def-base-change-map` gives the same exchange on the square with sides exchanged; I recorded it in `blueprint.same_as`, without citing it as a dependency (which would create a cycle). Its own reference back to this item prevents merging here. Second-phrasing searches again found only generic mate infrastructure and unrelated Kaehler-differential base-change results. The generic mate source at Mathlib/CategoryTheory/Adjunction/Mates.lean:84 does not itself construct the derived module functors.

## Second reading by NO

- Item statement: compared every object, hypothesis and arrow with the master blueprint `def-kun-unbounded-exchange.md` (order 1664) and Stacks 07A7, `sites-cohomology.tex`, `remark-base-change`: correct. All schemes and the arbitrary commutative coefficient ring remain; no boundedness, properness or torsion hypothesis was added. The two displayed composites have the correct sources and targets.
- Proof steps: none, correctly, because this item defines a morphism rather than asserting invertibility or another theorem. `proof`, `proof_deps` and `citations.json` are empty; no theorem content was transferred to a child.
- New nodes: none; B1–B7 and the elementary/duplicate/restatement/Mathlib-child audit therefore have no new-node cases.
- `def-weil-pbc-cartesian-square`: opened its statement and checked the four edge directions, chosen fibre-product identification and comparison orientation; correct.
- `def-weil-pbc-derived-categories`: opened its statement; it defines the unbounded constant-ring module categories, with the abelian-sheaf case at Z; correct.
- `prop-weil-pbc-inverse-image-modules-exact`: opened all three clauses and Stacks 04JC, `sites-modules.tex`, `lemma-flat-pullback-exact`; the module inverse image is exact and adjoint for every constant commutative ring, not only Z; correct.
- `def-weil-pbc-derived-inverse-image`: opened the statement; its unbounded termwise functor and module extension provide the convention, while the following general exact-functor lemma supplies the unbounded derivability; correct, without using a bounded-below-only clause for unbounded existence.
- `lem-weil-pbc-exact-functor-derived-functor`: opened clause (1) and Stacks 015F, `derived.tex`, `lemma-right-derived-exact-functor`; exact inverse image computes its total left derived functor on every complex; correct.
- `def-weil-pbc-kinjective-resolutions`: opened the statement; I is a complex in the same module category and K is represented by a complex with a quasi-isomorphism to I; correct interpretation of K to QI.
- `prop-weil-pbc-kinjective-resolutions-exist`: opened the statement and Stacks 079P, `injectives.tex`, `theorem-K-injective-embedding-grothendieck`; supplies resolutions, not by itself the derived adjunction; correct use in the repaired first-worker draft.
- `lem-weil-pbc-kinjective-total-derived`: opened the statement and Stacks 070K, `derived.tex`, `lemma-enough-K-injectives-implies`; apply to the triangulated functor Q composed with termwise u_* on the homotopy category, giving Ru_*K represented by u_*I; correct. Additivity makes termwise u_* commute with shifts and mapping cones, so this input is triangulated even though sheaf u_* need not be exact.
- `lem-pc-derived-adjoint-functors`: opened the statement and Stacks 09T5, `derived.tex`, `lemma-derived-adjoint-functors`; RF is everywhere defined by K-injectives and LG by exactness, so both hypotheses are present; correct.
- Module square comparison: the abelian comparison is module-linear because naturality at each multiplication endomorphism m_lambda gives theta_M composed with f'^{-1}g^{-1}(m_lambda) equal to g'^{-1}f^{-1}(m_lambda) composed with theta_M. The constant-ring identifications and actions are clause (1) and (2) of the module inverse-image proposition. In each degree naturality at d gives theta_{M^{r+1}} composed with d equal to d composed with theta_{M^r}; hence this is an isomorphism of complexes. These are elementary two-line checks, not additional lemma nodes.
- `lem-weil-pbc-localization-universal-property`: opened clause (2); apply it to Q of the two termwise composites, with the exact-functor comparison isomorphisms. Exactness preserves quasi-isomorphisms and the inverse comparison descends too; correct.
- `def-weil-pbc-derived-square-iso`: opened its full statement; it explicitly constructs the unbounded abelian square isomorphism before restricting to D^+. The item uses it only at Lambda = Z, not as a module theorem; correct.
- `def-weil-pbc-adjunction-mate`: opened its statement and Mathlib `CategoryTheory/Adjunction/Mates.lean:84`; take L1=f^{-1}, R1=Rf_*, L2=f'^{-1}, R2=Rf'_*, G=g^{-1}, H=g'^{-1}. Its component formula is exactly the displayed unit-square-counit composite; correct.
- `def-weil-pbc-derived-exchange`: opened its statement; cited only for the identical formula, with the unbounded module ingredients supplied independently, not for unbounded existence; correct.
- Edge cases: for an identity square the square comparison is the identity and the adjunction triangle identity makes exchange the identity under the canonical identifications. For K=0 all three arrows are the unique maps of zero objects. For an empty scheme the corresponding module category is zero and the arrows remain defined; for a field coefficient ring and complexes concentrated in degree 0 or 1 the same formula applies. There is no n parameter or invertibility claim to test.
- Duplicate/source audit: searched DAG statements for unbounded exchange and opened `sbc-def-base-change-map`; its exchanged-square formula is the same construction, but it cites this item, so citing it here would create a cycle. Retaining the recorded `blueprint.same_as` without a dependency is correct. Read the chapter and Kunneth unit source; no unit or chapter route was changed.
- Lean/Mathlib audit: read slopmaster2 `SixFunctors/BaseChange/DerivedUnbounded.lean:97-126` and the adjunction at `Etale/Derived/UpperLowerStar.lean:401-404`. The generic definition uses abstract coefficient-category and flat-resolution instances and a derived composition comparison; it is a candidate requiring coefficient and comparison identification, not a direct attachment of the stated constant-module construction. The archived upstream master does not contain that DerivedUnbounded file; it was not treated as proof evidence. Independent LeanFinder and Loogle queries with Beck–Chevalley/TwoSquare vocabulary returned only generic mates; inspected Mathlib mateEquiv at line 84. The actual CategoryTheory grep returned 25 displayed generic base-change/stability hits, with no exact derived etale module exchange.

Changes and reasons:

- Removed `split_report.tool_uses`: accepted tool-use recording belongs to the maintainer (C8). The generic dependencies serve the exact inverse-image construction, localization, K-injective computation and adjunction needed here; the Kunneth unit has no replacements. They remain statement dependencies, and this review explains their use.
- Made the two previous grep queries verbatim equal to their logged patterns and recorded the three independently executed searches with their actual results. An earlier second-reader grep accidentally supplied `--sub` as a positional directory; that raw log entry is preserved but is not evidence of absence and is not recorded in the node. The corrected positional CategoryTheory search is the evidence used above.
- Added this independent, dependency-by-dependency reading. The mathematical statement and all correct first-worker sections are unchanged. No statement dispute was found.
