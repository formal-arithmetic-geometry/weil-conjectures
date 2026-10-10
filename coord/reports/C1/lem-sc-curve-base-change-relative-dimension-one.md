## Files written

- `dag/nodes/sec-picard-framework/lem-sc-curve-base-change-relative-dimension-one.json`: repaired step 3 and its dependencies.
- `dag/nodes/sec-picard-framework/lem-sc-dimension-locally-algebraic.json`: new unsplit statement node for Stacks Tag 0A21 part (3), with no Mathlib match.
- `citations.json`: verbatim citations for every node used by every proof step.

## Attachments

None. The item has no sorry-free declaration in slopmaster2.

## WANTED

None.

## Issues found

The returned delivery correctly identified that the old step 3 treated the global dimension clause of `def-pc-curve` as a pointwise statement. I added the reusable Stacks 0A21 node and changed step 3 to use `lem-pc-scheme-dimension-local-rings` to convert the curve's `def-pc-dimension` value into topological dimension, then 0A21 to identify every `dim_y(C)`. The step now explicitly identifies the fibre of `C -> Spec k` over its unique base point with `C`, so the `X_s` in the 02FY node is the stated curve. I also corrected step 2 to cite `def-pc-scheme-fibre`, whose statement defines scheme-theoretic fibres.

## Review by C1

I read the returned item, the imported blueprint proof step (4) in `literature/blueprint/master/blueprint/sec-picard-framework/sk-prop-jacobian/_section.md`, and the Stacks sources `morphisms.tex` Tags 02NK and 02FY and `varieties.tex` Tag 0A21 part (3). I read the statement of every cited node. Step 1 uses clause (2) of `lem-pc-proper-base-change`, which states smoothness is stable under base change, and `def-sbc-smooth-morphisms`, which defines the target relative-dimension notion. Step 2 uses the base-change and scheme-theoretic-fibre definitions to identify the fibre with `C x_{Spec k} Spec kappa(t)`. Step 3 uses the 02FY node for the local fibre-dimension equality, `def-pc-curve` for global dimension one, `lem-pc-scheme-dimension-local-rings` for equality of topological and local-ring dimensions, and the new 0A21 node for pointwise dimension on an irreducible locally finite-type scheme. I verified that a curve is integral and finite type, hence irreducible and locally finite type, and that `Spec k` has its unique point with residue field `k`. Step 4 is the direct definition check from `def-sbc-smooth-morphisms`.

For the new node I searched the whole DAG and blueprint for Tag 0A21 and for locally algebraic dimension statements; no duplicate exists. Its statement introduces the field, the irreducible scheme, the locally finite type structure morphism, nonempty opens, points, and both dimension notions with their definition nodes. I ran the required LeanSearch, LeanFinder, and Mathlib source grep searches; they found only component ingredients (`topologicalKrullDim`, stalk coheight, and subspace inequalities), not the 0A21 theorem. I checked the corrected step and every citation against the exact node statements and recorded each quote in `citations.json`.

## What could not be finished

The 0A21 node is intentionally statement-only and remains unsplit for a later stage-1 worker.
