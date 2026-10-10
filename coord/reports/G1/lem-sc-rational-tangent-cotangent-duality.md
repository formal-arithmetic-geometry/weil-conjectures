# Stage-1 worker report

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-rational-tangent-cotangent-duality.json`: split item.
- `dag/nodes/sec-picard-framework/lem-sc-rational-point-tangent-identification.json`: new unsplit statement node; Mathlib searches found no match.

## Attachments

None. The Lean source has no declaration tagged `lem-sc-rational-tangent-cotangent-duality` and no sorry-free declaration with this statement.

## WANTED

None. `literature/stacks-project/varieties.tex` is present and contains Tags 0B2E, 0B2C and 0B2F.

## What I checked and changed

The item source is Stacks Project `varieties.tex`, Tag 0B2E (rational-point tangent space), with functoriality from Tag 0B2C and the map comparison in Tag 0B2F. I also read `def-sc-scheme-tangent-space.json`, whose statement defines the dual-number tangent space and the tangent map, and the existing `lem-sc-point-tangent-cotangent-surjective.json`, which depends on this item. No exact declaration exists in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`; `AlgebraicGeometry.TangentSpace` only defines relative tangent sheaves.

The new node states only the single-point canonical identification, with all objects and rationality hypotheses introduced. Step 1 of the item applies that statement separately at `x` and `y`; its cited node says exactly the identification used. Step 2 uses the tangent-map clause of `def-sc-scheme-tangent-space` and the same identification node: the local-ring map sends `m_y` to `m_x`, and composition of a dual-number lift with `f` is precomposition by the induced quotient map, hence the dual map. The cited statements were copied verbatim into `citations.json`.

I searched the DAG and blueprint for an existing rational-point tangent/cotangent identification and found none. I searched Mathlib with LeanSearch, Loogle, and source grep for the scheme tangent-space identification; only ring-level cotangent declarations appeared, so the new node remains unsplit. Small checks: for `Spec k`, both cotangent and tangent spaces are zero; for `A^1_k` at the origin, both are one-dimensional and the identification is the usual coefficient-of-`ε` map; for `t ↦ t^2` at the origin, both induced maps are zero, confirming the naturality direction.

## Review by G1

I checked the item and new node against `varieties.tex` Tags 0B2E, 0B2C and 0B2F, and read the full statements of every cited DAG node. Step 1 cites only the single-point identification, whose hypotheses match `κ(x)=κ(y)=k`; step 2 cites the explicit dual-number tangent-map definition and the same identification, and the remaining passage to precomposition is the direct local-ring calculation. The item statement depends on the scheme conventions, tangent-space definition, and identification node. The new node is statement-only as required for an unsplit node, introduces `X`, `x`, `k`, the local maximal ideal, and the tangent space itself, and records all three required Mathlib search kinds. I corrected the initial empty proof by making the two source arguments explicit and added exact citation quotes for both steps.

## What was wrong or incomplete

The imported item had no proof or split metadata despite being used by the already reviewed cotangent-surjectivity lemma. The Lean implementation has no corresponding theorem; its tangent-space file concerns relative tangent sheaves only.

## What remains

The narrower identification node is intentionally unsplit because it is not a Mathlib declaration and is a separate queue item for a later worker.
