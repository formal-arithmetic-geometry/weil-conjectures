## Worker report

Restated by reviewer R-ttr (statement correction reverted).

The delivered statement correction is reverted (H7): it replaced the node by the existence of three free morphisms i, j, k making some triangle distinguished, which is weaker than Stacks Remark 08J5 itself (the remark asserts the *canonical* triangle with the canonical maps) and drops the clauses the citers use (def-weil-pbc-truncation-exact-couples builds its couple from i_q, j_q, k_q; lem-weil-pbc-truncation-couple-morphism needs the functoriality). The node's extra clauses (uniqueness of k_q, functoriality in D(A), bounded below) are true and proved in the node from BBD 1.1.9/1.1.10 (ii) and the standard t-structure vanishing Hom(D^{<=q-2}, D^{>=q}) = 0.

`DerivedCategory.truncation_triangle` (lean/Sheaf/CategoryTheory/TruncationTriangle.lean) states the sheaf-dag node:
1. for every complex K: i_q, j_q are morphisms of complexes tied to the canonical ones (i ≫ ιTruncLE q = ιTruncLE (q-1); degree-q component of j is truncLEXIsoCycles ≫ homologyπ, the same characterizations as the landed `truncation_descends`), and there is a unique k with `Triangle.mk (Q.map i) (Q.map j) k ∈ distTriang`;
2. the three functors tau_{<=q-1}, tau_{<=q}, H^q(-)[-q] are inverted-by-Q (they preserve quasi-isomorphisms after Q) and, acting on f : Q K ⟶ Q L through the canonical localization lift `Localization.lift … Q` with `Localization.fac`, give a morphism of triangles T_q(K) → T_q(L) (three squares);
3. strictly / cohomologically bounded-below K gives bounded-below terms (IsStrictlyGE / IsGE n for the truncations, min n q for the single complex).
Proof left as sorry (stage 2).

## Second reading by V1

Superseded by reviewer R-ttr: the second reading corrected the node to a bare existence of three free morphisms; this was reverted with --revert-statement and the Lean restated to the sheaf-dag node as above.
