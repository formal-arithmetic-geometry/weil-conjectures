# Delivery report

1. files written

- `dag/nodes/sec-curve-estimates/lem-sc-component-intersections-finite.json`: item, statement node, split; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-noetherian-closed-points-finite.json`: new statement node, unsplit; no Mathlib match.

2. attachments

- None. No sorry-free slopmaster2 declaration states the item or the new node exactly.

3. WANTED

- None. The cited source is available in the local Stacks checkout at `/home/ubuntu/c1-stacks-review/varieties.tex`.

4. corrections and limitations

- The imported item was unsplit and had the correct substantive statement. I retained its hypotheses and conclusion.
- The proof now follows Varieties Lemma 09NX, first proof paragraph. It explicitly separates (i) finiteness of the component family, (ii) closedness of points in a proper component intersection, and (iii) finiteness of the resulting closed subset, followed by the finite-union and uniqueness conclusion.
- The supporting node `lem-sc-noetherian-closed-points-finite` is deliberately statement-only as a newly created unsplit node. Its statement is self-contained and uses only the Noetherian and quasi-compact scheme notions. It packages the elementary Noetherian-space argument: finitely many irreducible components, each an irreducible set of closed points and therefore a singleton.

## Review by H1

I read the source paragraph of Varieties Lemma 09NX in `/home/ubuntu/c1-stacks-review/varieties.tex` (the label `lemma-dim-1-noetherian-reduced-separated-has-ample`, lines 8080 onward). The source says that a Noetherian one-dimensional scheme has finitely many irreducible components, that the union of pairwise intersections is finite and consists of closed points, and that points outside this union lie on a unique component. The item statement agrees with those conclusions and states the dimension condition topologically, as its cited definition requires.

For step 1 I checked the cited statement of `lem-weil-pbc-noetherian-finitely-many-components`: it says exactly that a Noetherian scheme has finitely many irreducible components, and records Mathlib's `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian` as an exact leaf. This is a generic tool from another unit and is declared in `tool_uses`.

For step 2 I checked the statement of `lem-sc-dim-one-point-outside-open-closed`: in an irreducible Kolmogorov space of dimension at most one, every point outside a nonempty open has closed singleton. For distinct components, the generic point of the first cannot lie on the second, so its complement in the first is a nonempty open; every point of the intersection is outside that open. A component is a closed subscheme, so closedness in the component gives closedness in the ambient scheme. The dimension bound is inherited by a closed subspace, and the component is irreducible and Kolmogorov as required.

For step 3 I checked the new node's statement: it is precisely the residual finiteness claim needed after step 2, with all objects and hypotheses introduced. It is supported by Properties Lemma 0BA8's finite irreducible-component theorem together with the elementary fact that an irreducible T0 subspace whose points are all closed is a singleton. The intersection is closed, so the node applies; the finite union over the finite ordered-pair family is finite; the uniqueness assertion follows directly from the definition of T.

I searched the DAG and blueprint for the item and for the new statement before writing. The only matching existing facts were the finite-component Mathlib leaf and the dimension-one closed-point node cited above; no node states the new closed-point finiteness statement. I tested the statements on the empty scheme, a reduced point, an integral affine curve (one component, empty intersection union), a disjoint union of a point and a curve, and two affine lines meeting in one point. These cases cover zero, one, and multiple components and confirm that T and the uniqueness conclusion have the stated behavior. Mathlib searches for the new node used LeanSearch, LeanFinder, and source grep; none supplied an exact theorem.

