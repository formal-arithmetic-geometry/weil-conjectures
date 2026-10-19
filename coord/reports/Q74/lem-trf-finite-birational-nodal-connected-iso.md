1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-finite-birational-nodal-connected-iso.json` — the item, split with five proof steps and no new child nodes; no Mathlib match.
- `citations.json` — verbatim statement excerpts for every cited node in every step.

2. Attachments: none. No declaration under `WeilConjectures/` states this item exactly without `sorry`.

3. WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, Appendix B, ordinary-point characterization and Lemma 4.4.2 local nodal argument; the URL is recorded in the imported node, but the PDF is not present in this checkout.

4. No statement or blueprint correction was needed. The item is not duplicated in the DAG. I did not create a child node: the local calculation is a direct step using the existing `lem-trf-ordinary-point-delta-branches` statement, while the component and affine-local arguments use existing normalization and finite-birational nodes. No SGA source is used.

5. The final dry run is the remaining check; no Lean source was written and no compiler or Lake command was run.

## Review by Q74

I read the imported item, its `lean_audit` fields, the `sk-i-curve-zero` unit, and the ancestor blueprint route under `lem-trf-local-term-locality`. I also read the full statements of `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-noetherian-finitely-many-components`, `lem-weil-pbc-finite-algebra-is-integral`, `def-sc-normalization`, `lem-sc-normalization-properties`, `lem-sc-smooth-normal`, `lem-trf-finite-birational-normal-iso`, and `lem-trf-ordinary-point-delta-branches`; each citation in the five steps takes exactly the quoted assertion. Step 1 checks that the open meeting every component contains all generic points and therefore gives a component bijection and function-field identifications. Step 2 checks integrality of each finite component map, places its structure sheaf between the target and the component normalization, and applies the normal-target isomorphism on the smooth locus. Step 3 applies the ordinary-node clause with exactly two branches and one-dimensional normalization quotient; the source stalk quotient is a k-subspace, so it is either zero or the whole quotient. Step 4 checks the latter case gives the two-point normalization fibre, which is disconnected because the finite fibre is a finite k-scheme and k is algebraically closed; this contradicts the stated geometric-fibre hypothesis. Step 5 is the affine-local conclusion from equality of the finite pushforward structure sheaf. I checked the empty-node case, the identity map, and the normalization of a nodal curve as the excluded disconnected-fibre edge case. The recorded Mathlib searches found only generic normalization/finiteness declarations and no combined theorem.
