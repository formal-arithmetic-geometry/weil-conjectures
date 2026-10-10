1. Files written:

   - `dag/nodes/sec-algebraic-groups-lie-algebras/def-wf-lie-algebra-derivation.json` (repaired definition).
   - `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-lie-algebra-derivation-bracket.json` (statement-only lemma; no Mathlib match).

2. Attachments:

   - `AlgebraicGeometry.tangentGroup` belongs to `def-wf-lie-algebra-derivation` (WeilConjectures/AlgebraicGeometry/GroupScheme/Lie.lean:842-847).
   - `AlgebraicGeometry.GrpObj.Lie` belongs to `def-wf-lie-algebra-derivation` (Lie.lean:161-165).
   - `AlgebraicGeometry.GeneralLinearGroup.lieAlgebraEquivMatrix` belongs to `def-wf-lie-algebra-derivation` (GeneralLinear/Lie.lean:120-123).
   - `AlgebraicGeometry.GeneralLinearGroup.RationalHom` and `.differential` belong to the corresponding rational-action clauses (GeneralLinear/Lie.lean:146-150, 174-179).

3. WANTED:

   None.

4. What was wrong and what changed:

   The returned item redefined `T_xX` as `(m_x/m_x^2)^dual`, duplicated the dual-number and derivation identifications, asserted bracket closure and differential compatibility without a DAG lemma, and redefined regularity and smoothness with an uncited dimension inequality. I changed `T_xX` to the established `T_{X/k,x}` of `def-sc-scheme-tangent-space`, restored `Lie(G)=T_{G/k,1}` and its dual-number identification, and made the Lie algebra and representation clauses cite their exact definitions and the bracket lemma. I retained the two rational-point descriptions as cited remarks and cited the existing regularity/smoothness definitions and equivalence lemmas. The bracket lemma is now self-contained and does not cite the item, avoiding the dependency cycle; later Lie-algebra arguments can cite it directly.

## Review by G1

I read the returned node, the complete statements of `def-sc-scheme-tangent-space`, `def-sc-dual-numbers`, `lem-sc-rational-tangent-cotangent-duality`, `lem-sc-rational-point-tangent-derivation-identification`, `def-wf-lie-algebra`, `def-wf-algebraic-representations`, `def-weil-regular-scheme`, `def-weil-pbc-smooth-ring-map`, `lem-weil-pbc-regular-local-cotangent-dimension`, `lem-weil-pbc-smooth-over-field-regular-local`, and `lem-weil-pbc-regular-local-separable-residue-smooth`. The revised statement uses exactly the objects those nodes define and now explicitly connects the tangent space to `Lie(G)`. I checked that every imported notion named in the statement appears in `stmt_deps`, and that the bracket lemma has no dependency back to the item. I reran LeanFinder, Loogle, and Mathlib grep for the new lemma and recorded the no-exact-match results in its `mathlib_searches`. The old inline dimension inequality and duplicate definitions were removed, and the item/lemma dependency direction was checked for cycles.

## Second reading by G1

- Item statement: checked against the imported tangent-space, dual-number, rational-point identification, Lie algebra, rational representation, regularity, and smoothness nodes; verdict: definitions and hypotheses are aligned, with `Lie(G)=T_1G` and the dual-number identification explicit.
- No new lemma remains: the proposed bracket node was checked against the item and identified as a restatement of two item clauses (D1), so it was removed.
- No proof steps remain in the definition node, so there are no hidden step citations to validate; the Milne Chapter 10 reference is retained only as the source for the standard bracket and differential facts stated in the definition.

Changes made in this second reading:

- Removed `lem-wf-lie-algebra-derivation-bracket.json` because it duplicated the item's own bracket-closure and differential-compatibility clauses.
- Removed that node from `stmt_deps` and replaced its citations with the explicit Milne Chapter 10 source remark.
- Rechecked the zero group, the trivial one-dimensional representation, and `GL_1`: all tangent, bracket, and differential clauses reduce to the expected zero or scalar cases.
