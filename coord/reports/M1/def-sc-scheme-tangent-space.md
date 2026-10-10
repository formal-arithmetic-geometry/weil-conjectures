1. Files written

- `dag/nodes/sec-picard-framework/def-sc-scheme-tangent-space.json`: definition, split; the general dual-number tangent-space definition is not a Mathlib leaf.
- `dag/nodes/sec-picard-framework/def-sc-dual-numbers.json`: definition, Mathlib leaf (`DualNumber`, `DualNumber.eps`).
- `citations.json`: empty list, because the item is a definition with no proof steps.

2. Attachments

None.

3. WANTED:

None.

4. Issues found

The item had only a broad grep search recorded and its dual-number constituent was not represented by a DAG node. I added the dual-number Mathlib leaf and made it an explicit statement dependency. The source formulation allows an arbitrary residue field and defines tangent vectors by maps from `Spec kappa[epsilon]`; the existing Lean `AlgebraicGeometry.tangentSpaceAt` is restricted to k-rational points, so it does not attach to this item.

5. Unfinished work

Nothing remains for this split. The vector-space operations and functorial tangent map are part of the item's stated definition, sourced from the cited Stacks definitions and lemmas; they are not separately proved nodes because this item is a definition node.

## Review by M1

I read the copied item and its source metadata, including Varieties Tags 0B29 (dual numbers), 0B2B (vector-space structure), 0B2C (tangent-space definition), and 0B2F (map on tangent spaces). I searched the whole DAG and blueprint for dual-number and tangent-space nodes and checked the Lean source in both the read-only source checkout and the slopmaster2 checkout. The only relevant Lean declaration, `AlgebraicGeometry.tangentSpaceAt`, has the narrower rational-point statement and therefore is not an exact attachment.

There are no proof steps in this definition node, so `citations.json` is correctly empty and there are no step hypotheses to verify. The new node states only the dual-number object and cites Mathlib's `DualNumber` and `DualNumber.eps`; I checked the declarations in `Mathlib/Algebra/DualNumber.lean` (the abbreviation at line 46 and epsilon definition at line 50), and recorded LeanSearch, LeanFinder, Loogle, and source-grep searches. I tested the edge case `R = k` for a field and verified that the Mathlib construction supplies the required square-zero epsilon. The item retains its existing scheme, residue-field, and affine-spectrum dependencies, and its blueprint ancestry and source places are preserved.
