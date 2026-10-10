Files written:

- `dag/nodes/sec-picard-framework/lem-sc-affine-maximal-points-closed-in-lft-scheme.json`: statement item, classified as a Mathlib leaf via `Topology.IsOpenEmbedding.preimage_closedPoints`.
- `citations.json`: empty because a Mathlib leaf has no natural-language proof steps.

Attachments: none.

WANTED: none.

The item has no exact declaration in the slopmaster2 Lean source. Its conclusion is a one-line specialization of Mathlib's `Topology.IsOpenEmbedding.preimage_closedPoints`; Lean infers the required `JacobsonSpace X` instance from `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` for `X -> Spec k` (with `Spec k` Jacobson). The existing item statement and its hypotheses were retained unchanged. No new DAG node was needed.

## Review by J1

I read the item record and the unit route in `sk-thm-picard-rr`, and checked the source reference to Varieties Tag 0478 (lemma-locally-finite-type-Jacobson). I searched the slopmaster2 source for the item tag and for declarations about affine-open maximal points; no exact declaration exists. I also searched the DAG and blueprint for an existing node with this statement and found none.

For the Mathlib classification, I read `Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean` at line 117 and `Mathlib/Topology/JacobsonSpace.lean` at line 127. The matched declaration is `Topology.IsOpenEmbedding.preimage_closedPoints` (line 127); its `JacobsonSpace X` hypothesis is supplied by the inferred instance from `AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace` (line 117), with the field base instance for `Spec k`. An affine open subscheme has an open embedding into `X`, so this is a one-line specialization. I checked the edge cases `X = Spec k` and `U = X`, where the conclusion is immediate, and `X = Spec k[t]`, where maximal ideals on an affine open are the usual closed points.

The required LeanFinder, Loogle, grep, and LeanSearch commands were run and their actual results are recorded in `mathlib_searches`; LeanSearch was unavailable. I removed the two incorrectly recorded empty grep results and retained the earlier reviewer grep record. Since the item is a Mathlib leaf, there are no proof steps or cited DAG statements, so `citations.json` is empty.
