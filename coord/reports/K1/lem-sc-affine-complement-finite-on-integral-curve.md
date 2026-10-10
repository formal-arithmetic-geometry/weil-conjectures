1. Files written:

   - `dag/nodes/sec-curve-estimates/lem-sc-affine-complement-finite-on-integral-curve.json`: item split; no new nodes.
   - `citations.json`: verbatim statements for both non-elementary citations.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof. I checked the Stacks Varieties Lemma 09ND context and its sentence that the complements of the chosen nonempty affine opens are finite. The stronger universal statement in this item follows directly from the existing topological and Noetherian finiteness nodes, so no duplicate node was created. The existing sorry-free Lean theorem `AlgebraicGeometry.IsCurve.exists_isAffineOpen_finite_compl` was not attached because it states existence of one affine open, not the item's universal statement for every nonempty affine open.

## Review by K1

I read the item source reference in `literature/stacks-project/varieties.tex` (Varieties Lemma 09ND) and checked every hypothesis against the item: integrality supplies irreducibility and the scheme's Kolmogorov property, the dimension hypothesis is $1\\leq1$, and the chosen affine open is nonempty. Step 1 is elementary: the complement of an open is closed. Step 2 cites `lem-sc-dim-one-point-outside-open-closed`; its statement explicitly takes an irreducible Kolmogorov space of dimension at most one, a nonempty open subset, and a point outside it, and concludes that the singleton is closed. Step 3 cites `lem-sc-noetherian-closed-points-finite`; its statement explicitly concludes finiteness for a closed subset all of whose points are closed. I copied both statements verbatim into `citations.json` and verified the cited node files exist and are unmerged. I tested the edge cases $U=X$ (empty finite complement) and an affine open in $\\mathbf P^1$ (one-point complement). No statement or dependency correction beyond adding the proof and split metadata was needed.
