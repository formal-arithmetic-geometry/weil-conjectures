# Delivery report

## Files written

- `dag/nodes/sec-curve-estimates/lem-sc-dim-one-quasi-projective.json` — item, statement split into three proof steps; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-dim-one-ample-invertible.json` — new unsplit statement node; no Mathlib match.

## Attachments

None. The slopmaster2 declaration `AlgebraicGeometry.IsCurve.isQuasiProjective` was checked in `WeilConjectures/AlgebraicGeometry/Curve/Compactification.lean:217-223`; it has `sorry` and its bundled `IsCurve`/`Smooth` hypotheses do not state this item exactly.

## WANTED

WANTED: `literature/stacks-project/varieties.tex`, Lemma 0A25 and Proposition 33.38.12 (Tag 09NZ), for `lem-sc-dim-one-quasi-projective` and `lem-sc-dim-one-ample-invertible`.

WANTED: `literature/stacks-project/morphisms.tex`, Lemma 01VS and Definition 29.41.1, for the projective immersion criterion used by `lem-sc-dim-one-quasi-projective`.

## What was checked and corrected

The imported item already had the exact separated finite-type, dimension-at-most-one statement from Stacks Lemma 0A25, so I left its statement and statement dependencies unchanged. The proof was missing. I searched all DAG nodes and the source checkout by the item id, the Stacks tag, and quasi-projectivity terms. The existing `lem-sc-curves-quasi-projective` is a different smooth-curve statement with an informal gluing proof, while `AlgebraicGeometry.IsCurve.isQuasiProjective` is sorry-bearing Lean; neither can be attached.

The non-elementary first step is the ample-sheaf existence assertion used verbatim in 0A25. I made it a separate, strictly smaller unsplit node (`lem-sc-dim-one-ample-invertible`) so the item does not hide that theorem. Its statement introduces the field, scheme, separated finite-type structure morphism, dimension bound, and the absolute ample-invertible-module notion. I checked the source tag and the dimension-zero edge case against the 0A25 conclusion; the node is deliberately unsplit because the local Stacks source is unavailable. I recorded LeanSearch, LeanFinder, and Mathlib-source grep searches; Mathlib has no algebraic-geometric ample/invertible-sheaf API.

For item step 1, the cited node states exactly the ample invertible sheaf needed. For step 2, the cited existing node `lem-weil-pbc-ample-very-ample-immersion-affine-base` states that an ample invertible module over an affine base yields an immersion into a finite-coordinate projective space; specializing the base to `Spec(k)` uses the given finite-type hypothesis and the elementary fact that `Spec(k)` is affine. For step 3, the cited immersion definitions supply the closed/open factorization and hence the requested `U`, closed immersion, and open immersion over `k`. `proof_deps` is exactly the union of the step citations, and the item remains `status: split` with an agent proof origin because the cited Stacks files are not present locally.

## Review by F1

I read the imported item, its blueprint ancestor `lem-sc-pic-proper-ntorsion`, the chapter/unit records, the Stacks tag index, the existing `lem-sc-proper-dim-one-projective` proof, and the source declarations around `IsCurve.isQuasiProjective`. I also inspected the existing affine-base ample-to-immersion node and its Morphisms 01VS source route. The item hypotheses match 0A25: a field base, separated finite-type structure morphism, and topological dimension at most one. The new node states only the preceding ample-sheaf conclusion and cites its own definition nodes.

Step 1 uses the new node's exact ample-sheaf statement; no elementary work is hidden there. Step 2 uses the existing 01VS-derived criterion and checks the only specialization: the base `Spec(k)` is affine and finite type implies locally finite type. Step 3 uses only the definition of an immersion to expose the closed immersion followed by the open immersion required by the item. I checked that no step relies on the proof of a cited node, that every cited node exists and says the fact used, and that the new node is strictly smaller than the item rather than a restatement.

I tested edge cases while checking the statement: the empty scheme and zero-dimensional finite-type schemes satisfy the ≤1 hypothesis and are covered by the Stacks quasi-projectivity conclusion; no nonempty or dimension-one assumption was accidentally added. The source checkout under `literature/stacks-project/` is absent, so the report records the precise WANTED documents and the proof origin is marked agent-written. Mathlib searches found no matching theorem. JSON parsing succeeds for both files; the delivery preflight will perform the repository-wide DAG, route, citation, and blueprint checks before push.

## Could not finish

No proof obligation remains in this split. The only unavailable inputs are the local Stacks source files listed under WANTED; the statements and citations were checked against the indexed tags and the public Stacks pages.
