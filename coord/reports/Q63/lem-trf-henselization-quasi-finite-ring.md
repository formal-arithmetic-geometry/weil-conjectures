Files written:

- `dag/nodes/sec-trace-formula/lem-trf-henselization-quasi-finite-ring.json` — statement, split proof, no new nodes, Mathlib searches found no exact theorem.
- `citations.json` — verbatim statement citations for every proof-step dependency.

Attachments: none.

WANTED: none.

No new nodes were created. The existing DAG already contains the ordinary-henselization ind-etale lemma, the four-rings quasi-finite base-change lemma, the henselian finite-type factor decomposition, the finite-local henselian lemma, ind-etale stability, principal-localization etaleness, and residue-compatible maps into henselian colimits. The imported item statement agrees with Stacks Tag 05WP: the finite-type condition is the finite-type clause in the quasi-finite-at-prime hypothesis, and the localization is at the prime induced by the chosen prime of B.

## Review by Q63

I read the item source and the complete Tag 05WP proof in `literature/stacks-project/algebra.tex`, together with Tags 00PN (four rings), 04GJ (henselian finite-type factor decomposition), 04GH (finite-over-henselian), 04GN/04GQ (ordinary henselization), 08HR (maps from ind-etale colimits into henselian local rings), and 00U2/097K for the ind-etale localization and composition facts. I also read the full statements of every cited DAG node and checked that the quotes in `citations.json` are verbatim.

Step 1 constructs the canonical local map from the universal property of the two ordinary henselizations, defines the tensor ring and its prime kernel, and checks the contractions to the maximal ideal and to q. Step 2 verifies the four-rings hypotheses: the tensor map is the symmetry isomorphism, the original map is finite type and quasi-finite at q, and the resulting base-changed map is quasi-finite at the selected prime. Step 3 applies the stated henselian factor decomposition; the selected prime cannot lie in the non-quasi-finite factor, and the finite factor's residue-domain argument makes it maximal, so its localization is finite local and henselian by the cited finite-local lemma. Step 4 checks both comparison rings are ind-etale over B: the henselization ind-etale theorem handles R and H, base-change and composition handle the tensor ring, and the explicit filtered principal-localization presentation handles D. Step 5 applies the residue-identity case of the henselian-colimit mapping theorem in both directions; uniqueness makes the two local maps inverse and preserves the canonical map from R. Step 6 writes the localization universal property explicitly, since elements of B outside q already map outside the tensor prime, yielding the exact localization in the item.

I checked edge cases including the identity map, a quotient map by an ideal in a local ring, an empty fibre, and a finite etale algebra with several local factors. In each case the selected factor/localization and the claimed finite local map behave as stated. No statement correction, source error, duplicate split, or new dependency was needed.
