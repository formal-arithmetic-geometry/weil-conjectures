# Stage-1 report: lem-per-noetherian-affine-line-unit

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-affine-line-unit.json`: existing statement node split in place; no new nodes.
- `citations.json`: 19 step/citation pairs, each quote copied verbatim from the cited node statement.

## Attachments

No new Lean attachments. I searched the read-only slopmaster2 source for the item id and for affine-line/noetherian homotopy-invariance declarations. The only nearby declaration is `AlgebraicGeometry.Etale.cohomology_affineLine_unit` in `WeilConjectures/FourierTransform/ArtinSchreierCohomology.lean:66`, which assumes an algebraically closed field and has a `sorry`; it does not state this item.

## WANTED

None. The cited ILO Exposé XVI PDF and the cited Stacks sources are present under `literature/`.

## What was wrong or incomplete

The imported item had a complete statement but no proof and `status: unsplit`; its source pointed to ILO Exposé XVI, Proposition 1.5, whose local argument invokes affine-line homotopy invariance without expanding the derived-category map. I left the statement unchanged, including the arbitrary Noetherian base and the absence of regularity or a map to a field.

I expanded the proof in seven steps. Steps 1–3 set up the projective-line charts, the normalized finite-coefficient projective-line adjunction, and the coordinate calculation for its unit and trace. Step 4 composes the infinity-section closed immersion adjunction with the projective-line adjunction and uses uniqueness of right adjoints to identify its support counit. Step 5 applies the ordinary closed/open support triangle and obtains a triangle `K -> Lambda_B \oplus K -> Rp_* Lambda_{A1_B} -> K[1]` whose first map has second coordinate the identity. Step 6 gives the explicit split-triangle argument and constructs the inverse to the first-coordinate map. Step 7 identifies that map with the canonical composite adjunction unit for `p=q\circ j`, using the normalized derived direct-image composition comparison.

Every cited node was opened and its statement copied into `citations.json`; the proof uses only what those statements provide. The Noetherian hypotheses were checked explicitly: projective-line properness and finite type over a Noetherian base imply its total space is Noetherian. The finite Tate line is locally free of rank one, so the dual/tensor and shift cancellations used in the projective-line adjunction are valid. I tested the split-triangle algebra on the edge case `K=0` and on `B=Spec(Z[1/ell])`; the construction reduces to the identity unit in both cases. No new node was necessary: the projective-line adjunction, support triangle, proper projection formula, derived composition, Hom exactness, and coefficient-line pullback are existing nodes.

## Review by Q100

I read the item node, its chapter `dag/chapters/sec-deligne-laumon-a1.json`, its unit `dag/units/sk-p-dl-a1-perverse.json`, the ILO PDF at Exposé XVI Proposition 1.5 (printed page 227), the projective-line adjunction blueprint proof, the closed-support-triangle proof, and every existing node cited by the seven proof steps. For step 1 I verified the two projective charts, the infinity closed immersion and affine-line complement, properness, and the Noetherian conclusion from the cited chart, properness, and finite-type statements. For step 2 I checked the exact hypotheses of the finite ordinary Tate-twist pullback and the normalized projective-line adjunction, including the proper projection formula and the dual evaluation. For step 3 I checked that the first coordinate of the projective-line decomposition is the ordinary unit and that the specified counit cancels the projection-formula comparison and trace. For step 4 I checked the directions of both adjunctions, the composite counit, and the uniqueness-of-right-adjoint conclusion. For step 5 I checked the support triangle, its image under the triangulated derived direct image, the composition comparison, and the identity of the second coordinate. For step 6 I checked each Hom-exactness factorization and the sign in the split-triangle inverse calculation. For step 7 I checked that the resulting first-coordinate map is exactly the canonical composite unit, using the normalized derived composition and exact inverse-image hypotheses.

I ran the required Mathlib searches for the item with LeanSearch, LeanFinder (two phrasings), Loogle, and Mathlib grep; all returned only unrelated algebraic-geometry or homological declarations, so this is not a Mathlib leaf. I recorded the actual queries and results in `searches.jsonl` and in the node's `mathlib_searches`. There are no duplicate new nodes and no source error to report. The item now has `status: split`, complete proof steps, exact `proof_deps`, blueprint metadata, and citation quotes.
