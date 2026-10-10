Files written:

- `dag/nodes/sec-picard-framework/lem-pc-affine-finite-type-algebra.json`: statement, one proof step, and split metadata; no new nodes.

Attachments:

- None.

WANTED:

- None.

What was checked and corrected:

- I read the item, its unit `sk-thm-picard-rr`, and the ancestor blueprint reference `lem-pc-degree-base-change`. The source is Stacks Morphisms, Tag 01T2, implication (1) to (2). The statement is unchanged and its existing `stmt_deps` name the scheme, finite-type morphism, and finite-type algebra notions.
- The sole proof step first unpacks the finite-type hypothesis using `def-weil-finite-type-morphism`, then applies `lem-weil-pbc-lft-affine-pairs` to the affine pair consisting of the whole source `Y` and the whole base `Spec k`. That cited statement explicitly supplies a finite-type ring map on every such affine pair, so its specialization gives `k -> Gamma(Y,O_Y) = B` and hence finite generation. The exact portions used are recorded verbatim in `citations.json`.
- I searched the whole DAG and blueprint for a duplicate statement and found none. I searched slopmaster2 for the item tag and relevant affine finite-type declarations; no sorry-free declaration states this item exactly. The existing affine-pairs node is Mathlib-backed, with its Lean declaration and source checked in `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`.
- Small cases checked: `Y = Spec k` gives `B = k`; `Y = Spec(k[e]/(e^2))` gives a finitely generated algebra; finite disjoint unions of affine points remain finite type; the empty affine scheme gives the zero algebra. `A^1_k` is excluded from the zero-dimensional application but still satisfies the finite-type conclusion.

What could not be finished:

- Nothing; no new child node was required.

## Review by K1

I checked the item against Stacks Morphisms Tag 01T2 and read the existing affine-pairs node in full. Step 1 uses the finite-type definition to obtain locally finite type, then uses the affine-pairs statement exactly for the affine opens `U = Y` and `V = Spec k`; that statement explicitly concludes that the induced map on sections is a finitely generated algebra. I verified the hypotheses that `Y` is affine, `Spec k` is affine, and the image inclusion is automatic. I checked the exact quoted sentences in `citations.json`, searched for duplicate DAG or blueprint statements, and verified the Mathlib source declaration behind the cited leaf. I corrected the report to include this review section after the first preflight identified it as required.
